{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
module Frontend.Declassify where

import Control.Monad.State
import Data.Bifunctor
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.List
import Data.Monoid
import Data.Ord
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Vector as Vector
import Data.Void

import Error
import Syntax
import Syntax.Concrete.Scoped
import Util
import VIX

declassify
  :: QName
  -> SourceLoc
  -> TopLevelPatDefinition Expr Void
  -> Maybe (Type Void)
  -> VIX
    ( [(QName, SourceLoc, TopLevelPatDefinition Expr Void, Maybe (Type Void))]
    , [(QName, SourceLoc, TopLevelPatDefinition Expr Void, Maybe (Type Void))]
    )
declassify name loc def mtyp = case (def, mtyp) of
  (TopLevelPatDefinition _, _) -> doNothing
  (TopLevelPatDataDefinition _, _) -> doNothing
  (TopLevelPatClassDefinition methods, Just typ) -> first pure <$> declass name loc methods typ
  (TopLevelPatClassDefinition _, Nothing) -> error "declassify impossible 1"
  (TopLevelPatInstanceDefinition methods, Just typ) -> flip (,) mempty <$> deinstance name loc methods typ
  (TopLevelPatInstanceDefinition _, Nothing) -> error "declassify impossible 2"
  where
    doNothing = return (pure (name, loc, def, mtyp), mempty)

{-
  class C a where
    f : T

  ==>

  type C a = MkC T
  f : forall a. C a => T
  f (MkC f') = f'
-}
declass
  :: QName
  -> SourceLoc
  -> ClassDef Expr Void
  -> Type Void
  -> VIX
    ( (QName, SourceLoc, TopLevelPatDefinition Expr Void, Maybe (Type Void))
    , [(QName, SourceLoc, TopLevelPatDefinition Expr Void, Maybe (Type Void))]
    )
declass qname loc classDef typ = do
  liftVIX $ modify $ \s -> s
    { vixClassMethods
      = HashMap.insert qname (Vector.fromList $ methodNames classDef)
      $ vixClassMethods s
    }
  let classConstrName = classConstr qname
      (params, _retType) = extractParams typ
      numMethods = length $ classMethods classDef
      implicitPiParams = quantify (\h _ t s -> Pi Implicit (AnnoPat (VarPat h ()) $ abstractNone t) $ mapBound (\() -> 0) s) params
      classType = apps (Global qname) $ iforTele params $ \i _ p _ -> (p, pure $ B $ TeleVar i)
      classParam = Pi Constraint (AnnoPat (VarPat mempty ()) $ abstractNone classType) . abstractNone
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
              (AnnoPat (VarPat (fromName mname) ()) (Scope $ pure . F $ unscope mtyp))
            . abstractNone)
          classType
        $ classMethods classDef
      , Just typ
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
        , Just $ implicitPiParams $ toScope $ classParam $ fromScope mtyp
        )
      | (i, MethodDef mname mloc mtyp) <- zip [0..] $ classMethods classDef
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

  instanceName-f = fbody

  instanceName : C a => C [a]
  instanceName = MkC instanceName-f
-}
deinstance
  :: QName
  -> SourceLoc
  -> PatInstanceDef Expr Void
  -> Type Void
  -> VIX [(QName, SourceLoc, TopLevelPatDefinition Expr Void, Maybe (Type Void))]
deinstance qname@(QName modName name) loc (PatInstanceDef methods) typ = located loc $ do
  className <- getClass typ
  mnames <- liftVIX $ gets $ HashMap.lookup className . vixClassMethods
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
      else do
        let mname n = QName modName $ name <> "-" <> n
        return $
          ( qname
          , loc
          , TopLevelPatDefinition
            $ PatDefinition
              Concrete
              IsInstance
              $ pure
              $ Clause mempty
              $ abstractNone
              $ apps (Con $ HashSet.singleton $ classConstr className)
              $ (\(n, _, _, _) -> (Explicit, global $ mname n)) <$> methods'
          , Just typ
          )
          :
          [ (mname n, loc', TopLevelPatDefinition def, mtyp)
          | (n, loc', def, mtyp) <- Vector.toList methods'
          ]
  where
    diff xs ys = HashSet.toList $ HashSet.difference (toHashSet xs) (toHashSet ys)
    duplicates xs = map head $ filter p $ group $ Vector.toList xs
      where
        p [] = False
        p [_] = False
        p _ = True
    getName (n, _, _, _) = n

getClass
  :: Expr v
  -> VIX QName
getClass (Pi _ _ s) = getClass $ fromScope s
getClass (SourceLoc loc e) = located loc $ getClass e
getClass (appsView -> (Global g, _)) = return g
getClass _ = throwInvalidInstance

throwInvalidInstance :: VIX a
throwInvalidInstance
  = throwLocated
  $ PP.vcat
  [ "Invalid instance"
  , "Instance types must return a class"
  , bold "Expected:" PP.<+> "an instance of the form" PP.<+> dullGreen "instance ... => C as where ..." <> ", where" PP.<+> dullGreen "C" PP.<+> "is a class."
  ]

throwMethodProblem :: QName -> [Name] -> [Name] -> [Name] -> VIX a
throwMethodProblem className missingMethods extraMethods duplicates
  = throwLocated
  $ PP.vcat
  $ "Invalid instance"
  : (concat $
    [ if null missingMethods then [] else ["The instance is missing an implementation for:" PP.<+> prettyHumanList "and" (red . pretty <$> missingMethods) <> "."]
    , if null extraMethods then [] else ["The" PP.<+> dullGreen (pretty className) PP.<+> "class does not define:" PP.<+> prettyHumanList "and" (red . pretty <$> extraMethods) <> "."]
    , if null duplicates then [] else ["Duplicate implementations for:" PP.<+> prettyHumanList "and" (red . pretty <$> duplicates) <> "."]
    ])
