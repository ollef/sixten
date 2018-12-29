{-# LANGUAGE FlexibleContexts, MonadComprehensions, OverloadedStrings, ViewPatterns #-}
module Elaboration.TypeCheck.Class where

import Protolude hiding (diff, typeRep)

import Control.Monad.Identity
import qualified Data.HashSet as HashSet
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Vector(Vector)

import qualified Builtin.Names as Builtin
import Driver.Query
import Effect
import Elaboration.Constraint
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
import TypedFreeVar
import qualified TypeRep
import Util

checkClassDef
  :: FreeV
  -> ClassDef Pre.Expr FreeV
  -> Elaborate (ClassDef (Core.Expr MetaVar) FreeV)
checkClassDef classVar (ClassDef params ms) = do
  -- TODO: These vars are typechecked twice (in checkAndGeneraliseDefs as the
  -- expected type and here). Can we clean this up?
  paramVars <- forTeleWithPrefixM params $ \h p s paramVars -> do
    let t = instantiateTele pure paramVars s
    t' <- withVars paramVars $ checkPoly t Builtin.Type
    forall h p t'

  withVars paramVars $ do
    runUnify (unify [] (Core.pis paramVars Builtin.Type) $ varType classVar) report

    ms' <- forM ms $ \(Method mname mloc s) -> do
      let typ = instantiateTele pure paramVars s
      typ' <- checkPoly typ Builtin.Type
      return $ Method mname mloc typ'

    return $ classDef paramVars ms'

{-
  class C a where
    f : T

  ==>

  type C a = MkC T
  f : forall a. C a => T
  f (MkC f') = f'
-}
desugarClassDef
  :: FreeV
  -> QName
  -> SourceLoc
  -> ClassDef (Core.Expr MetaVar) FreeV
  -> Elaborate (Vector (FreeV, GName, SourceLoc, Definition (Core.Expr MetaVar) FreeV))
desugarClassDef classVar name loc (ClassDef params ms) = do
  paramVars <- forTeleWithPrefixM params $ \h p s paramVars -> do
    let t = instantiateTele pure paramVars s
    forall h p t

  let ms' = [Method mname mloc $ instantiateTele pure paramVars s | Method mname mloc s <- ms]

  let implicitParamVars = (\v -> v { varData = implicitise $ varData v }) <$> paramVars
      qcon = classConstr name
      abstr = teleAbstraction paramVars
      classType = Core.apps (pure classVar) $ (\v -> (varData v, pure v)) <$> paramVars
      classConstrType = foldr
        (\(Method mname _ mtyp) -> Core.Pi (fromName mname) Explicit mtyp . abstractNone)
        classType
        ms'

      sizes = methodExpr <$> ms'
      typeRep = foldl' productType (Core.MkType TypeRep.UnitRep) sizes

  typeRep' <- whnfExpandingTypeReps typeRep

  let classDataDef
        = DataDefinition
          (DataDef
            (varTelescope paramVars)
            [ConstrDef (qconstrConstr qcon) $ abstract abstr classConstrType]
          )
        $ Core.lams paramVars typeRep'

  conArgVars <- forM ms' $ \(Method mname _ t) ->
    forall (fromName mname) Explicit t

  lamVar <- forall mempty Constraint classType

  methodDefs <- forM (zip conArgVars ms') $ \(v, Method mname mloc mtyp) -> do
    let fullType = Core.pis implicitParamVars $ Core.pi_ lamVar mtyp
        mdef
          = ConstantDefinition Concrete
          $ Core.lams implicitParamVars
          $ Core.lam lamVar
          $ Core.Case
            (pure lamVar)
            (ConBranches [conBranchTyped qcon (toVector conArgVars) $ pure v])
            fullType
    var <- forall (fromName mname) Explicit fullType
    return (var, gname $ QName (qnameModule name) mname, mloc, mdef)

  return $ pure (classVar, gname name, loc, classDataDef) <> toVector methodDefs

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
  :: FreeV
  -> QName
  -> SourceLoc
  -> Pre.InstanceDef Pre.Expr FreeV
  -> Elaborate (Vector (FreeV, GName, SourceLoc, Definition (Core.Expr MetaVar) FreeV))
checkInstance ivar iname iloc (Pre.InstanceDef _instanceType methods) =
  runIdentityT $ deepSkolemiseInner (varType ivar) mempty $ \skolemVars innerInstanceType skolemFun -> IdentityT $ do
    innerInstanceType' <- whnf innerInstanceType
    case Core.appsView innerInstanceType' of
      (Builtin.QGlobal className, args) -> do
        maybeClassDef <- getClassDef className
        case maybeClassDef of
          Nothing -> return mempty
          Just (ClassDef _params methodDefs) -> do
            let names = methodName <$> methodDefs
                methods' = sortOn (hashedElemIndex (toVector names) . methodName) methods
                names' = methodName <$> methods'
            if names /= names' then do
              -- TODO more fine-grained recovery
              reportMethodProblem
                className
                (diff names names')
                (diff names' names)
                (duplicates names')
              return mempty
            else do
              methodDefs' <- forM (zip methodDefs methods')
                $ \(Method name _defLoc defType, Method _name loc (Pre.ConstantDef a clauses mtyp)) -> located loc $ do
                  let instMethodType
                        = instantiateTele snd (toVector args) defType
                  expr <- case mtyp of
                    Nothing -> checkClauses clauses instMethodType
                    Just typ -> do
                      typ' <- checkPoly typ Builtin.Type
                      expr <- checkClauses clauses typ'
                      f <- subtype typ' instMethodType
                      return $ f expr
                  v <- forall (fromName name) Explicit $ Core.pis skolemVars instMethodType
                  let gn = GName iname $ pure name
                  return (v, gn, loc, ConstantDefinition a $ Core.lams skolemVars expr)
              let skolemArgs = (\v -> (varData v, pure v)) <$> skolemVars
                  methodArgs = (\(v, _, _, _) -> (Explicit, Core.apps (pure v) skolemArgs)) <$> methodDefs'
                  implicitArgs = first implicitise <$> args
              return
                $ pure
                  ( ivar
                  , gname iname
                  , iloc
                  , ConstantDefinition Concrete
                    $ skolemFun
                    $ Core.lams skolemVars
                    $ Core.apps (Core.Con $ classConstr className) $ implicitArgs <> methodArgs
                  )
                <> toVector methodDefs'
      _ -> do
        reportInvalidInstance
        return mempty
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
        DataDefinition (DataDef params [ConstrDef _constr scope]) _rep -> do
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
