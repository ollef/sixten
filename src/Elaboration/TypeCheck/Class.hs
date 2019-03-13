{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module Elaboration.TypeCheck.Class where

import Protolude hiding (diff, typeRep)

import qualified Data.HashSet as HashSet
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import qualified Builtin.Names as Builtin
import Driver.Query
import Effect
import qualified Effect.Context as Context
import Elaboration.Constraint
import Elaboration.MetaVar.Zonk
import Elaboration.MetaVar
import Elaboration.Monad
import Elaboration.Subtype
import Elaboration.TypeCheck.Clause
import Elaboration.TypeCheck.Data
import Elaboration.TypeCheck.Expr
import Elaboration.Unify
import Syntax
import qualified Syntax.Core as Core
import qualified Syntax.Pre.Scoped as Pre
import qualified TypeRep
import Util

checkClassDef
  :: ClassDef Pre.Expr Var
  -> CoreM
  -> Elaborate (ClassDef (Core.Expr MetaVar) Var)
checkClassDef (ClassDef params ms) typ = do
  -- TODO: These vars are typechecked twice (in checkAndGeneraliseDefs as the
  -- expected type and here). Can we clean this up?
  logMeta "tc.class" "class type" $ zonk typ
  teleMapExtendContext params (`checkPoly` Builtin.Type) $ \paramVars -> do
    typ' <- Core.pis paramVars Builtin.Type
    runUnify (unify [] typ' typ) report

    ms' <- forM ms $ \(Method mname mloc s) -> do
      let
        methodType = instantiateTele pure paramVars s
      methodType' <- checkPoly methodType Builtin.Type
      return $ Method mname mloc methodType'

    classDef paramVars ms'

{-
  class C a where
    f : T

  ==>

  type C a = MkC T
  f : forall a. C a => T
  f (MkC f') = f'
-}
desugarClassDef
  :: Var
  -> QName
  -> SourceLoc
  -> ClassDef (Core.Expr MetaVar) Var
  -> Elaborate
    ( (Var, GName, SourceLoc, Definition (Core.Expr MetaVar) Var)
    , Vector (Var, GName, SourceLoc, Definition (Core.Expr MetaVar) Var, CoreM)
    )
desugarClassDef classVar name loc (ClassDef params ms) =
  teleExtendContext params $ \paramVars -> do
    let
      ms' = [Method mname mloc $ instantiateTele pure paramVars s | Method mname mloc s <- ms]

      plicitParamVars =
        Vector.zip (telePlics params) paramVars
      implicitParamVars =
        first implicitise <$> plicitParamVars

      qcon = classConstr name
      classType = Core.apps (pure classVar) $ second pure <$> plicitParamVars
      classConstrType = foldr
        (\(Method mname _ mtyp) -> Core.Pi (fromName mname) Explicit mtyp . abstractNone)
        classType
        ms'

      sizes = methodExpr <$> ms'
      typeRep = foldl' productType (Core.MkType TypeRep.UnitRep) sizes

    typeRep' <- whnfExpandingTypeReps typeRep
    parameterisedTypeRep <- Core.lams paramVars typeRep'

    dd <- dataDef Unboxed paramVars [ConstrDef (qconstrConstr qcon) classConstrType]

    let
      classDataDef = DataDefinition dd parameterisedTypeRep
      conArgBindings = foreach ms' $ \(Method mname _ t) ->
        binding (fromName mname) Explicit t
    Context.freshExtends conArgBindings $ \conArgVars -> do
      methodDefs <- forM (zip conArgVars ms') $ \(v, Method mname mloc mtyp) ->
        Context.freshExtend (binding mempty Constraint classType) $ \lamVar -> do
          fullType <- Core.plicitPis implicitParamVars =<< Core.pi_ lamVar mtyp
          br <- conBranch qcon (toVector conArgVars) $ pure v
          lam
            <- Core.lam lamVar
            $ Core.Case
              (pure lamVar)
              (ConBranches [br])
              fullType
          mdef
            <- ConstantDefinition Concrete
            <$> Core.plicitLams implicitParamVars lam
          var <- Context.freeVar
          return (var, gname $ QName (qnameModule name) mname, mloc, mdef, fullType)

      return
        ( (classVar, gname name, loc, classDataDef)
        , toVector methodDefs
        )

{-
  instanceName = instance C a => C [a] where
    f = fbody

  ==>

  instanceName-f = fbody

  instanceName : C a => C [a]
  instanceName =
    MkC instanceName-f
-}
checkInstance
  :: Var
  -> QName
  -> SourceLoc
  -> Pre.InstanceDef Pre.Expr Var
  -> CoreM
  -> Elaborate
    ( (Var, GName, SourceLoc, Definition (Core.Expr MetaVar) Var)
    , Vector (Var, GName, SourceLoc, Definition (Core.Expr MetaVar) Var, CoreM)
    )
checkInstance ivar iname iloc (Pre.InstanceDef _instanceType methods) typ =
  deepSkolemiseInner typ mempty $ \skolemVars innerInstanceType skolemFun -> do
    innerInstanceType' <- whnf innerInstanceType
    let
      errorInstance = do
        lam
          <- Core.lams skolemVars
          $ Builtin.Fail innerInstanceType'
        return ((ivar, gname iname, iloc, ConstantDefinition Concrete $ skolemFun lam), mempty)
    case Core.appsView innerInstanceType' of
      (Builtin.QGlobal className, args) -> do
        maybeClassDef <- getClassDef className
        case maybeClassDef of
          Nothing -> errorInstance
          Just (ClassDef _params methodDefs) -> do
            let
              names = methodName <$> methodDefs
              methods' = sortOn (hashedElemIndex (toVector names) . methodName) methods
              names' = methodName <$> methods'
            if names /= names' then do
              -- TODO more fine-grained recovery
              reportMethodProblem
                className
                (diff names names')
                (diff names' names)
                (duplicates names')
              errorInstance
            else do
              methodDefs' <- forM (zip methodDefs methods')
                $ \(Method name _defLoc defType, Method _name loc (Pre.ConstantDef a clauses msig)) -> located loc $ do
                  let
                    instMethodType
                      = instantiateTele snd (toVector args) defType
                  expr <- case msig of
                    Nothing -> checkClauses clauses instMethodType
                    Just sig -> do
                      typ' <- checkPoly sig Builtin.Type
                      expr <- checkClauses clauses typ'
                      f <- subtype typ' instMethodType
                      return $ f expr
                  fullType <- Core.pis skolemVars instMethodType
                  v <- Context.freeVar
                  let
                    gn = GName iname $ pure name
                  lam <- Core.lams skolemVars expr
                  return (v, gn, loc, ConstantDefinition a lam, fullType)
              ctx <- getContext
              let
                skolemArgs = (\v -> (Context.lookupPlicitness v ctx, pure v)) <$> skolemVars
                methodArgs = (\(v, _, _, _, _) -> (Explicit, Core.apps (pure v) skolemArgs)) <$> methodDefs'
                implicitArgs = first implicitise <$> args
              lam
                <- Core.lams skolemVars
                $ Core.apps (Core.Con $ classConstr className)
                $ implicitArgs <> methodArgs
              return
                ( ( ivar
                  , gname iname
                  , iloc
                  , ConstantDefinition Concrete $ skolemFun lam
                  )
                , toVector methodDefs'
                )
      _ -> do
        reportInvalidInstance
        errorInstance
  where
    diff xs ys = HashSet.toList $ HashSet.difference (toHashSet xs) (toHashSet ys)
    duplicates xs = mapMaybe p $ group xs
      where
        p [] = Nothing
        p [_] = Nothing
        p (x:_:_) = Just x

getClassDef :: QName -> Elaborate (Maybe (ClassDef (Core.Expr meta) v))
getClassDef name = do
  mmnames <- fetch $ ClassMethods name
  case mmnames of
    Nothing -> do
      reportInvalidInstance
      return Nothing
    Just mnames -> do
      def <- fetchDefinition $ gname name
      case def of
        ConstantDefinition {} -> panic "getClassDef constant"
        DataDefinition (DataDef _ params [ConstrDef _constr scope]) _rep -> do
          let types = methodTypes $ fromScope scope
          return $ Just $ ClassDef params $ zipWith (\(n, loc) typ -> Method n loc $ toScope typ) (toList mnames) types
        DataDefinition DataDef {} _ -> panic "getClassDef datadef"
  where
    methodTypes (Core.Pi _ _ t1 (unusedScope -> Just t2)) = t1 : methodTypes t2
    methodTypes _ = mempty

classConstr :: QName -> QConstr
classConstr qname@(QName _ name) = QConstr qname $ fromName $ "Mk" <> name

-- TODO duplicated here and in ResolveNames
reportInvalidInstance :: MonadReport m => m ()
reportInvalidInstance
  = reportLocated
  $ PP.vcat
  [ "Invalid instance"
  , "Instance types must return a class"
  , bold "Expected:" PP.<+> "an instance of the form" PP.<+> dullGreen "instance ... => C as where ..." <> ", where" PP.<+> dullGreen "C" PP.<+> "is a class."
  ]

reportMethodProblem
  :: MonadReport m
  => QName
  -> [Name]
  -> [Name]
  -> [Name]
  -> m ()
reportMethodProblem className missingMethods extraMethods duplicates
  = reportLocated
  $ PP.vcat
  $ "Invalid instance"
  : concat
    [ if null missingMethods then [] else ["The instance is missing an implementation for:" PP.<+> prettyHumanList "and" (red . pretty <$> missingMethods) <> "."]
    , if null extraMethods then [] else ["The" PP.<+> dullGreen (pretty className) PP.<+> "class does not define:" PP.<+> prettyHumanList "and" (red . pretty <$> extraMethods) <> "."]
    , if null duplicates then [] else ["Duplicate implementations for:" PP.<+> prettyHumanList "and" (red . pretty <$> duplicates) <> "."]
    ]
