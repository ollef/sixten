{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module Analysis.Simplify where

import Protolude hiding (Type)

import qualified Data.HashSet as HashSet
import qualified Data.MultiSet as MultiSet
import qualified Data.Vector as Vector

import Analysis.Termination
import qualified Builtin.Names as Builtin
import Driver.Query
import Effect
import qualified Effect.Context as Context
import Elaboration.Normalise
import SourceLoc
import Syntax
import Syntax.Core
import Util
import Util.Tsil(Tsil)
import qualified Util.Tsil as Tsil

type MonadSimplify m = (MonadFetch Query m, MonadFresh m, MonadContext (Expr Void Var) m)

simplifyDef
  :: MonadSimplify m
  => (GName -> Bool)
  -> Definition (Expr Void) Var
  -> m (Definition (Expr Void) Var)
simplifyDef glob (ConstantDefinition a e) = ConstantDefinition a <$> simplifyExpr glob e
simplifyDef glob (DataDefinition (DataDef b ps cs) t) = do
  t' <- simplifyExpr glob t
  teleMapExtendContext ps (simplifyExpr glob) $ \vs -> do
    cs' <- forM cs $ \(ConstrDef c s) ->
      ConstrDef c <$> simplifyExpr glob (instantiateTele pure vs s)
    DataDefinition <$> dataDef b vs cs' <*> pure t'

simplifyExpr
  :: MonadSimplify m
  => (GName -> Bool)
  -> Expr Void Var
  -> m (Expr Void Var)
simplifyExpr glob expr = go Nothing expr mempty
  where
    locApps = foldl (\e (mloc, p, e') -> maybe identity SourceLoc mloc $ App e p e')
    done mloc e es = return $ locApps (maybe identity SourceLoc mloc e) es
    go
      :: MonadSimplify m
      => Maybe SourceLoc
      -> Expr Void Var
      -> [(Maybe SourceLoc, Plicitness, Expr Void Var)]
      -> m (Expr Void Var)
    go mloc e@(Var _) es = done mloc e es
    go _ (Meta m _) _ = absurd m
    go mloc e@(Global n) es
      | glob n = do
        me' <- fetch $ InlinedDefinition n
        case me' of
          Nothing -> done mloc e es
          Just (Biclosed e') -> go mloc e' es
      | otherwise = done mloc e es
    go mloc Builtin.Zero es = done mloc (Lit $ Natural 0) es
    go mloc (Con Builtin.SuccConstr) ((mloc', Explicit, Lit (Natural n)):es) = done (mloc <|> mloc') (Lit $ Natural $ n + 1) es
    go mloc e@(Con _) es = done mloc e es
    go mloc e@(Lit _) es = done mloc e es
    go mloc (Pi h p t s) es = do
      t' <- simplifyExpr glob t
      Context.freshExtend (Context.binding h p t') $ \v -> do
        e <- simplifyExpr glob $ instantiate1 (pure v) s
        res <- pi_ v e
        done mloc res es
    go _ (Lam h p t s) ((appLoc, p', e):es)
      | p == p' = do
        t' <- simplifyExpr glob t
        letBody <- Context.freshExtend (Context.binding h p t') $ \v ->
          let_ (pure (v, fromMaybe (noSourceLoc "simplify") appLoc, e)) $ instantiate1 (pure v) s
        go appLoc letBody es
      | otherwise = panic "simplify Lam mismatched plicitness"
    go mloc e@Lam {} [] = etaLams glob mloc mempty e
    go mloc (App e1 p e2) es = do
      e2' <- simplifyExpr glob e2
      go Nothing e1 $ (mloc, p, e2') : es
    go mloc (Case e brs retType) es = do
      e' <- simplifyExpr glob e
      case chooseBranch e' brs of
        Nothing -> do
          brs' <- simplifyBranches glob brs
          retType' <- simplifyExpr glob retType
          done mloc (Case e' brs' retType') es
        Just chosen -> go mloc chosen es
    go mloc (Let ds s) es = letRec mloc ds s es
    go mloc (ExternCode c retType) es = do
      c' <- mapM (simplifyExpr glob) c
      retType' <- simplifyExpr glob retType
      done mloc (ExternCode c' retType') es
    go _ (SourceLoc loc e) es = go (Just loc) e es

    letRec
      :: MonadSimplify m
      => Maybe SourceLoc
      -> LetRec (Expr Void) Var
      -> Scope LetVar (Expr Void) Var
      -> [(Maybe SourceLoc, Plicitness, Expr Void Var)]
      -> m (Expr Void Var)
    letRec mloc ds scope es =
      letMapExtendContext ds (simplifyExpr glob) $ \vs -> do
        let
          toMultiSet = foldMap MultiSet.singleton
          body = instantiateLet pure vs scope
          occs = toMultiSet body <> fold (forLet ds $ \_ _ s t ->
            toMultiSet (instantiateLet pure vs s) <> toMultiSet t)
        ds' <- iforMLet ds $ \i _ loc s _ -> do
          e <- simplifyExpr glob $ instantiateLet pure vs s
          return (vs Vector.! i, loc, e)
        let
          (inline, ds'')
            = Vector.partition
              (\(v, _, e) -> duplicable e || MultiSet.occur v occs <= 1 && terminates glob e)
              ds'
          sub e = e >>= \v -> fromMaybe (pure v) $ lookupInline v
          lookupInline = hashedLookup $ (\(v, _, e) -> (v, sub e)) <$> inline
          ds''' = foreach ds'' $ \(v, loc, e) -> (v, loc, sub e)
        body' <- go Nothing (sub body) es
        result <- let_ ds''' body'
        return $ maybe identity SourceLoc mloc result

etaLams
  :: MonadSimplify m
  => (GName -> Bool)
  -> Maybe SourceLoc
  -> Tsil (Maybe SourceLoc, Var)
  -> Expr Void Var
  -> m (Expr Void Var)
etaLams glob mloc vs (Lam h p t s) = do
  t' <- simplifyExpr glob t
  Context.freshExtend (Context.binding h p t') $ \v ->
    etaLams glob Nothing (Tsil.Snoc vs (mloc, v)) $ instantiate1 (pure v) s
etaLams glob _ vs (SourceLoc loc e) =
  etaLams glob (Just loc) vs e
etaLams glob mlocation vars expr = do
  expr' <- simplifyExpr glob expr
  fromMaybe
    (maybe identity (fmap . SourceLoc) mlocation $ locLams vars expr')
    (go mlocation vars expr')
  where
    go
      :: MonadSimplify m
      => Maybe SourceLoc
      -> Tsil (Maybe SourceLoc, Var)
      -> Expr Void Var
      -> Maybe (m (Expr Void Var))
    go _ (Tsil.Snoc vs (_, v)) (App e1 _ (varView -> Just v'))
      | v == v'
      , not $ v `HashSet.member` toHashSet e1 = go Nothing vs e1
    go _ vs (SourceLoc loc e) = go (Just loc) vs e
    go mloc vs e
      | terminates glob e = Just $ maybe identity (fmap . SourceLoc) mloc $ locLams vs e
    go _ _ _ = Nothing

locLams
  :: (MonadContext (Expr meta Var) m, Foldable t)
  => t (Maybe SourceLoc, Var)
  -> Expr meta Var
  -> m (Expr meta Var)
locLams xs e = foldrM (uncurry locLam) e xs

locLam
  :: MonadContext (Expr meta Var) m
  => Maybe SourceLoc
  -> Var
  -> Expr meta Var
  -> m (Expr meta Var)
locLam mloc v e = maybe identity (fmap . SourceLoc) mloc $ lam v e

simplifyBranches
  :: MonadSimplify m
  => (GName -> Bool)
  -> Branches (Expr Void) Var
  -> m (Branches (Expr Void) Var)
simplifyBranches glob (ConBranches cbrs) =
  fmap ConBranches $ forM cbrs $ \(ConBranch qc tele s) ->
    teleMapExtendContext tele (simplifyExpr glob) $ \vs -> do
      e <- simplifyExpr glob $ instantiateTele pure vs s
      conBranch qc vs e
simplifyBranches glob (LitBranches lbrs def) =
  LitBranches
    <$> mapM (\(LitBranch l e) -> LitBranch l <$> simplifyExpr glob e) lbrs
    <*> simplifyExpr glob def
