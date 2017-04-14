{-# LANGUAGE OverloadedStrings #-}
module Syntax.Concrete.Literal where

import Data.ByteString as ByteString
import Data.Text(Text)
import Data.Text.Encoding as Encoding
import qualified Data.Vector as Vector

import Syntax
import Syntax.Concrete.Pattern
import Syntax.Concrete.Unscoped as Unscoped

import qualified Builtin

-- TODO: Be more precise in the names

string :: Text -> Expr Name
string
  = App (Var Builtin.MkStringName) Explicit
  . byteArray
  . Encoding.encodeUtf8

byteArray :: ByteString -> Expr Name
byteArray bs
  = Unscoped.apps (Var Builtin.MkArrayName)
  [ (Explicit, nat $ ByteString.length bs)
  , ( Explicit
    , App (Var Builtin.RefName) Explicit
    $ ByteString.foldr
      (\byte rest -> Unscoped.apps (Var Builtin.MkPairName) [(Explicit, Lit $ Byte byte), (Explicit, rest)])
      (Var Builtin.MkUnitConstrName)
      bs
    )
  ]

nat :: (Eq a, Num a) => a -> Expr Name
nat 0 = Var Builtin.ZeroName
nat n = App (Var Builtin.SuccName) Explicit (nat (n - 1))

stringPat :: Text -> Pat t Name
stringPat
  = ConPat (Right Builtin.MkStringConstr)
  . pure
  . (,) Explicit
  . byteArrayPat
  . Encoding.encodeUtf8

byteArrayPat :: ByteString -> Pat t Name
byteArrayPat bs = ConPat (Right Builtin.MkArrayConstr)
  $ Vector.fromList
  [ (Explicit, natPat $ ByteString.length bs)
  , (Explicit
    , ConPat (Right Builtin.Ref)
    $ pure
    $ ( Explicit
      , ByteString.foldr
        (\byte rest -> ConPat
          (Right Builtin.MkPairConstr)
          $ Vector.fromList [(Explicit, LitPat $ Byte byte), (Explicit, rest)])
        (ConPat (Right Builtin.MkUnitConstr) mempty)
        bs
      )
    )
  ]

natPat :: (Eq a, Num a) => a -> Pat t Name
natPat 0 = ConPat (Right Builtin.ZeroConstr) mempty
natPat n = ConPat (Right Builtin.SuccConstr) $ pure (Explicit, natPat (n - 1))
