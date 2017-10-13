{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
module Frontend.Declassify where

import Control.Monad.Except
import Control.Monad.State
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.List
import Data.Monoid
import Data.Ord
import qualified Data.Vector as Vector
import Data.Void
import qualified Text.PrettyPrint.ANSI.Leijen as Leijen
import Text.Trifecta.Result(Err(Err), explain)

import Syntax
import Syntax.Concrete.Scoped
import Util
import VIX

declassify
  :: QName
  -> SourceLoc
  -> TopLevelPatDefinition Expr Void
  -> Type Void
  -> VIX
    ( (QName, SourceLoc, TopLevelPatDefinition Expr Void, Type Void)
    , [(QName, SourceLoc, TopLevelPatDefinition Expr Void, Type Void)]
    )
declassify name loc def typ = case def of
  TopLevelPatDefinition _ -> doNothing
  TopLevelPatDataDefinition _ -> doNothing
  TopLevelPatClassDefinition methods -> declass name loc methods typ
  TopLevelPatInstanceDefinition methods -> flip (,) mempty <$> deinstance name loc methods typ
  where
    doNothing = return ((name, loc, def, typ), mempty)

{-
  class C a where
    f : T

  ==>

  type C a = MkC T
  f : forall {a}. C a => T
  f (MkC f') = f'
-}
declass
  :: QName
  -> SourceLoc
  -> ClassDef Expr Void
  -> Type Void
  -> VIX
    ( (QName, SourceLoc, TopLevelPatDefinition Expr Void, Type Void)
    , [(QName, SourceLoc, TopLevelPatDefinition Expr Void, Type Void)]
    )
declass qname loc classDef typ = do
  modify $ \s -> s
    { vixClassMethods
      = HashMap.insert qname (Vector.fromList $ methodNames classDef)
      $ vixClassMethods s
    }
  let classConstrName = classConstr qname
      (params, _retType) = extractParams typ
      numMethods = length $ classMethods classDef
      implicitPiParams = quantify (\h _ t s -> Pi Implicit (AnnoPat (abstractNone t) $ VarPat h ()) $ mapBound (\() -> 0) s) params
      classType = apps (Global qname) $ iforTele params $ \i _ p _ -> (p, pure $ B $ TeleVar i)
      classParam = Pi Constraint (AnnoPat (abstractNone classType) $ VarPat mempty ()) . abstractNone
  return
    (( qname
      , loc
      , TopLevelPatDataDefinition
        $ DataDef
        $ pure
        $ ConstrDef (qconstrConstr classConstrName)
        $ Scope
        $ foldr
          (\(MethodDef mname _ mtyp) ->
            Pi
              Explicit
              (AnnoPat (Scope $ pure . F $ unscope mtyp) (VarPat (fromName mname) ()))
            . abstractNone)
          classType
        $ classMethods classDef
      , typ
      )
    , [ ( QName (qnameModule qname) mname
        , mloc
        , TopLevelPatDefinition
          (PatDefinition
            Concrete
            IsOrdinaryDefinition
            $ pure
            $ Clause
              (pure (Constraint, ConPat (HashSet.singleton classConstrName) pats))
              $ toScope $ pure $ B $ B 0
          )
        , implicitPiParams $ toScope $ classParam $ fromScope mtyp
        )
      | (i, MethodDef mname (Hint mloc) mtyp) <- zip [0..] $ classMethods classDef
      , let prePats = Vector.replicate i WildcardPat
            postPats = Vector.replicate (numMethods - i - 1) WildcardPat
            pats = (,) Explicit <$> prePats <> pure (VarPat mempty ()) <> postPats
      ]
      )

classConstr :: QName -> QConstr
classConstr qname@(QName _ name) = QConstr qname $ fromName $ "Mk" <> name

extractParams
  :: Expr v
  -> (Telescope Plicitness Expr v, Scope TeleVar Expr v)
extractParams = bindingsView $ \expr -> case expr of
  Pi1 h p t s -> Just (h, p, t, s)
  _ -> Nothing

{-
  instanceName = instance C a => C [a] where
    f = fbody

  ==>

  instanceName : C a => C [a]
  instanceName = MkC fbody
-}
deinstance
  :: QName
  -> SourceLoc
  -> PatInstanceDef Expr Void
  -> Type Void
  -> VIX (QName, SourceLoc, TopLevelPatDefinition Expr Void, Type Void)
deinstance name loc (PatInstanceDef methods) typ = located loc $ do
  className <- getClass typ
  mnames <- gets $ HashMap.lookup className . vixClassMethods
  case mnames of
    Nothing -> throwInvalidInstance
    Just names -> do
      let methods'
            = Vector.fromList
            $ sortBy (comparing $ hashedElemIndex names . getName)
            $ Vector.toList methods
          names' = getName <$> methods'
      if names /= names' then
        throwMethodProblem
          className
          (diff names names')
          (diff names' names)
          (duplicates names')
      else
        return
          ( name
          , loc
          , TopLevelPatDefinition
            $ PatDefinition
              Abstract
              IsInstance
              $ pure
              $ Clause mempty
              $ abstractNone
              $ Let ((\(n, loc', def) -> (loc', fromName n, instantiateClause absurd <$> def, Scope Wildcard)) <$> methods')
              $ toScope
              $ apps (Con $ HashSet.singleton $ classConstr className)
              $ (\i -> (Explicit, pure $ B i)) <$> Vector.enumFromN 0 (Vector.length methods')
          , typ
          )
  where
    diff xs ys = HashSet.toList $ HashSet.difference (toHashSet xs) (toHashSet ys)
    duplicates xs = map head $ filter p $ group $ Vector.toList xs
      where
        p [] = False
        p [_] = False
        p _ = True
    getName = fst3

getClass
  :: Expr v
  -> VIX QName
getClass (Pi _ _ s) = getClass $ fromScope s
getClass (SourceLoc loc e) = located loc $ getClass e
getClass (appsView -> (Global g, _)) = return g
getClass _ = throwInvalidInstance

throwInvalidInstance :: VIX a
throwInvalidInstance = do
  loc <- currentLocation
  throwError
    $ show
    $ explain loc
    $ Err (Just "Invalid instance")
    [ "Instance types must return a class"
    , Leijen.bold "Expected:" Leijen.<+> "an instance of the form" Leijen.<+> Leijen.dullgreen "instance ... => C as where ..." <> ", where" Leijen.<+> Leijen.dullgreen "C" Leijen.<+> "is a class."
    ]
    mempty
    mempty

throwMethodProblem :: QName -> [Name] -> [Name] -> [Name] -> VIX a
throwMethodProblem className missingMethods extraMethods duplicates = do
  loc <- currentLocation
  throwError
    $ show
    $ explain loc
    $ Err (Just "Invalid instance")
    (concat $
      [ if null missingMethods then [] else ["The instance is missing an implementation for:" Leijen.<+> prettyHumanList "and" (Leijen.red . pretty <$> missingMethods) <> "."]
      , if null extraMethods then [] else ["The" Leijen.<+> Leijen.dullgreen (pretty className) Leijen.<+> "class does not define:" Leijen.<+> prettyHumanList "and" (Leijen.red . pretty <$> extraMethods) <> "."]
      , if null duplicates then [] else ["Duplicate implementations for:" Leijen.<+> prettyHumanList "and" (Leijen.red . pretty <$> duplicates) <> "."]
      ])
    mempty
    mempty
