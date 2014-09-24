{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts #-}
-- | Case branches
module Branches where

import Control.Applicative
import Data.Foldable
import Data.Traversable

import Bound
import Util

data Branches b v
  = ConBranches [ConBranch b v]       -- ^ Must be total
  | LitBranches [LitBranch b v] (b v) -- ^ Has default branch
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data ConBranch b v = ConBranch ECon Int (Scope Int b v)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
data LitBranch b v = LitBranch Literal (b v)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

mapBranches :: Functor b => (b v -> b v') -> Branches b v -> Branches b v'
mapBranches f (ConBranches brs) =
  ConBranches [ConBranch c i $ Scope $ fmap f <$> s | ConBranch c i (Scope s) <- brs]
mapBranches f (LitBranches brs d) =
  LitBranches [LitBranch n (f b) | LitBranch n b <- brs] (f d)

instance Bound Branches where
  ConBranches cbrs >>>= f = ConBranches (map (>>>= f) cbrs)
  LitBranches lbrs d >>>= f = LitBranches (map (>>>= f) lbrs) (d >>= f)

instance Bound ConBranch where
  ConBranch c i s >>>= f = ConBranch c i (s >>>= f)
instance Bound LitBranch where
  LitBranch n b   >>>= f = LitBranch n (b >>= f)

{-
instance (Monad e, Pretty (e v), Pretty v, IsString v) => Pretty (Branches e v) where
  prettyPrec ns d (ConBranches cbrs)     = vcat $ map (prettyPrec ns d) cbrs
  prettyPrec ns d (LitBranches lbrs def) =
       vcat $ map (prettyPrec ns d) lbrs
    ++ [text "_" <+> text "->" <+> prettyPrec ns 0 def]

instance (Monad e, Pretty (e v), Pretty v, IsString v) => Pretty (ConBranch e v) where
  prettyPrec ns d (ConBranch c numVars s) = prettyGenVars ns d numVars $ \fvs _ bvs lu ->
    prettyApps fvs 0 (prettyPrecF c) (map (\bv _ _ -> text bv) bvs) <+>
    text "->" <+> align (pretty fvs $ instantiate (return . lu) s)

instance (Pretty (e v), Pretty v, IsString v) => Pretty (LitBranch e v) where
  prettyPrec ns _ (LitBranch l e) =
    pretty ns l <+> text "->" <+> align (pretty ns e)
-}
