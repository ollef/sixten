{-# LANGUAGE OverloadedStrings #-}
module Syntax.Concrete.Literal where

import Data.ByteString as ByteString
import qualified Data.HashSet as HashSet
import Data.Text(Text)
import Data.Text.Encoding as Encoding
import qualified Data.Vector as Vector

import Syntax
import Syntax.Concrete.Pattern
import Syntax.Concrete.Unscoped as Unscoped

import qualified Builtin

string :: Text -> Expr QName
string
  = App (Var $ QName "Sixten.Builtin" $ fromConstr Builtin.MkStringName) Explicit
  . byteArray
  . Encoding.encodeUtf8

byteArray :: ByteString -> Expr QName
byteArray bs
  = Unscoped.apps (Var $ unqualified $ constrToName Builtin.MkArrayName)
  [ (Explicit, nat $ ByteString.length bs)
  , ( Explicit
    , App (Var $ unqualified $ constrToName Builtin.RefName) Explicit
    $ ByteString.foldr
      (\byte rest -> Unscoped.apps (Var $ unqualified $ constrToName Builtin.MkPairName) [(Explicit, Lit $ Byte byte), (Explicit, rest)])
      (Var $ unqualified $ constrToName Builtin.MkUnitConstrName)
      bs
    )
  ]

nat :: (Eq a, Num a) => a -> Expr QName
nat 0 = Var $ unqualified $ constrToName Builtin.ZeroName
nat n = App (Var $ unqualified $ constrToName Builtin.SuccName) Explicit (nat (n - 1))

stringPat :: Text -> Pat t v
stringPat
  = ConPat (HashSet.singleton Builtin.MkStringConstr)
  . pure
  . (,) Explicit
  . byteArrayPat
  . Encoding.encodeUtf8

byteArrayPat :: ByteString -> Pat t v
byteArrayPat bs = ConPat (HashSet.singleton Builtin.MkArrayConstr)
  $ Vector.fromList
  [ (Explicit, natPat $ ByteString.length bs)
  , (Explicit
    , ConPat (HashSet.singleton Builtin.Ref)
    $ pure
    ( Explicit
    , ByteString.foldr
      (\byte rest -> ConPat
        (HashSet.singleton Builtin.MkPairConstr)
        $ Vector.fromList [(Explicit, LitPat $ Byte byte), (Explicit, rest)])
      (ConPat (HashSet.singleton Builtin.MkUnitConstr) mempty)
      bs
    )
    )
  ]

natPat :: (Eq a, Num a) => a -> Pat t v
natPat 0 = ConPat (HashSet.singleton Builtin.ZeroConstr) mempty
natPat n = ConPat (HashSet.singleton Builtin.SuccConstr) $ pure (Explicit, natPat (n - 1))
