{-# LANGUAGE FlexibleContexts, MonadComprehensions, OverloadedStrings, ViewPatterns #-}
module Elaboration.TypeCheck.Class where

import Control.Monad.Except
import Control.Monad.State
import Data.Bifunctor
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.List
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Vector(Vector)

import qualified Builtin.Names as Builtin
import Elaboration.Constraint
import Elaboration.MetaVar
import Elaboration.Monad
import Elaboration.Subtype
import Elaboration.TypeCheck.Clause
import Elaboration.TypeCheck.Data
import Elaboration.TypeCheck.Expr
import Elaboration.Unify
import MonadContext
import Syntax
import qualified Syntax.Core as Core
import qualified Syntax.Pre.Scoped as Pre
import TypedFreeVar
import qualified TypeRep
import Util
import qualified Util.MultiHashMap as MultiHashMap
import VIX

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
    unify [] (Core.pis paramVars Builtin.Type) $ varType classVar

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
  -> Elaborate (Vector (FreeV, QName, SourceLoc, Definition (Core.Expr MetaVar) FreeV))
desugarClassDef classVar name loc def@(ClassDef params ms) = do
  liftVIX $ modify $ \s -> s
    { vixClassMethods
      = HashMap.insert name (methodLocNames def)
      $ vixClassMethods s
    }

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
    return (var, QName (qnameModule name) mname, mloc, mdef)

  return $ pure (classVar, name, loc, classDataDef) <> toVector methodDefs

{-
  instanceName = instance C a => C [a] where
    f = fbody

  ==>

  instanceName : C a => C [a]
  instanceName =
    let f = fbody
    MkC f
-}
checkInstance
  :: FreeV
  -> QName
  -> SourceLoc
  -> Pre.InstanceDef Pre.Expr FreeV
  -> Elaborate (Vector (FreeV, QName, SourceLoc, Definition (Core.Expr MetaVar) FreeV))
checkInstance ivar iname iloc (Pre.InstanceDef _instanceType methods) =
  deepSkolemiseInner (varType ivar) mempty $ \skolemVars innerInstanceType skolemFun -> do
    innerInstanceType' <- whnf innerInstanceType
    case Core.appsView innerInstanceType' of
      (Core.Global className, args) -> do
        liftVIX $ modify $ \s -> s
          { vixClassInstances
            = MultiHashMap.insert className iname
            $ vixClassInstances s
          }
        ClassDef _params methodDefs <- getClassDef className
        let names = methodName <$> methodDefs
            methods' = sortOn (hashedElemIndex (toVector names) . methodName) methods
            names' = methodName <$> methods'
        if names /= names' then
          -- TODO recover
          throwMethodProblem
            className
            (diff names names')
            (diff names' names)
            (duplicates names')
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
              let qname = QName (qnameModule iname) (qnameName iname <> "-" <> name)
              return (v, qname, loc, ConstantDefinition a $ Core.lams skolemVars expr)
          let skolemArgs = (\v -> (varData v, pure v)) <$> skolemVars
              methodArgs = (\(v, _, _, _) -> (Explicit, Core.apps (pure v) skolemArgs)) <$> methodDefs'
              implicitArgs = first implicitise <$> args
          return
            $ pure
              ( ivar
              , iname
              , iloc
              , ConstantDefinition Concrete
                $ skolemFun
                $ Core.lams skolemVars
                $ Core.apps (Core.Con $ classConstr className) $ implicitArgs <> methodArgs
              )
            <> toVector methodDefs'
      _ -> throwInvalidInstance
  where
    diff xs ys = HashSet.toList $ HashSet.difference (toHashSet xs) (toHashSet ys)
    duplicates xs = map head $ filter p $ group xs
      where
        p [] = False
        p [_] = False
        p _ = True

getClassDef :: QName -> Elaborate (ClassDef (Core.Expr meta) v)
getClassDef name = do
  mmnames <- liftVIX $ gets $ HashMap.lookup name . vixClassMethods
  case mmnames of
    Nothing -> throwInvalidInstance
    Just mnames -> do
      (def, _) <- definition name
      case def of
        ConstantDefinition {} -> internalError "getClassDef constant"
        DataDefinition (DataDef params [ConstrDef _constr scope]) _rep -> do
          let types = methodTypes $ fromScope scope
          return $ ClassDef params $ zipWith (\(n, loc) typ -> Method n loc $ toScope typ) mnames types
        DataDefinition DataDef {} _ -> internalError "getClassDef datadef"
  where
    methodTypes (Core.Pi _ _ t1 (unusedScope -> Just t2)) = t1 : methodTypes t2
    methodTypes _ = mempty

classConstr :: QName -> QConstr
classConstr qname@(QName _ name) = QConstr qname $ fromName $ "Mk" <> name

-- TODO duplicated here and in ResolveNames
throwInvalidInstance :: (MonadError Syntax.Error m, MonadVIX m) => m a
throwInvalidInstance
  = throwLocated
  $ PP.vcat
  [ "Invalid instance"
  , "Instance types must return a class"
  , bold "Expected:" PP.<+> "an instance of the form" PP.<+> dullGreen "instance ... => C as where ..." <> ", where" PP.<+> dullGreen "C" PP.<+> "is a class."
  ]

throwMethodProblem
  :: (MonadError Syntax.Error m, MonadVIX m)
  => QName
  -> [Name]
  -> [Name]
  -> [Name]
  -> m a
throwMethodProblem className missingMethods extraMethods duplicates
  = throwLocated
  $ PP.vcat
  $ "Invalid instance"
  : concat
    [ if null missingMethods then [] else ["The instance is missing an implementation for:" PP.<+> prettyHumanList "and" (red . pretty <$> missingMethods) <> "."]
    , if null extraMethods then [] else ["The" PP.<+> dullGreen (pretty className) PP.<+> "class does not define:" PP.<+> prettyHumanList "and" (red . pretty <$> extraMethods) <> "."]
    , if null duplicates then [] else ["Duplicate implementations for:" PP.<+> prettyHumanList "and" (red . pretty <$> duplicates) <> "."]
    ]
