{-# LANGUAGE OverloadedStrings #-}
module Syntax.Pre.Literal where

import Data.ByteString as ByteString
import Data.Text(Text)
import Data.Text.Encoding as Encoding
import qualified Data.Vector as Vector

import Syntax
import Syntax.Pre.Pattern
import Syntax.Pre.Unscoped as Unscoped

import qualified Builtin.Names as Builtin

string :: Text -> Expr
string
  = App (Var $ fromQConstr Builtin.MkStringConstr) Explicit
  . byteArray
  . Encoding.encodeUtf8

byteArray :: ByteString -> Expr
byteArray bs
  = Unscoped.apps (Var $ fromQConstr Builtin.MkArrayConstr)
  [ (Explicit, nat $ ByteString.length bs)
  , ( Explicit
    , App (Var $ fromQConstr Builtin.Ref) Explicit
    $ ByteString.foldr
      (\byte rest -> Unscoped.apps (Var $ fromQConstr Builtin.MkPairConstr) [(Explicit, Lit $ Byte byte), (Explicit, rest)])
      (Var $ fromQConstr Builtin.MkUnitConstr)
      bs
    )
  ]

nat :: (Eq a, Num a) => a -> Expr
nat 0 = Var $ fromQConstr Builtin.ZeroConstr
nat n = App (Var $ fromQConstr Builtin.SuccConstr) Explicit (nat (n - 1))

stringPat :: Text -> Pat PreName t v
stringPat
  = ConPat (fromQConstr Builtin.MkStringConstr)
  . pure
  . (,) Explicit
  . byteArrayPat
  . Encoding.encodeUtf8

byteArrayPat :: ByteString -> Pat PreName t v
byteArrayPat bs = ConPat (fromQConstr Builtin.MkArrayConstr)
  $ Vector.fromList
  [ (Explicit, natPat $ ByteString.length bs)
  , (Explicit
    , ConPat (fromQConstr Builtin.Ref)
    $ pure
    ( Explicit
    , ByteString.foldr
      (\byte rest -> ConPat
        (fromQConstr Builtin.MkPairConstr)
        $ Vector.fromList [(Explicit, LitPat $ Byte byte), (Explicit, rest)])
      (ConPat (fromQConstr Builtin.MkUnitConstr) mempty)
      bs
    )
    )
  ]

natPat :: (Eq a, Num a) => a -> Pat PreName t v
natPat 0 = ConPat (fromQConstr Builtin.ZeroConstr) mempty
natPat n = ConPat (fromQConstr Builtin.SuccConstr) $ pure (Explicit, natPat (n - 1))
