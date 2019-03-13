{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Frontend.DupCheck where

import Protolude hiding (TypeError)

import Control.Monad.State
import Data.Char
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.Text as Text
import qualified Data.Text.Prettyprint.Doc as PP

import Syntax
import qualified Syntax.Pre.Unscoped as Pre
import Util

data DupState = DupState
  { instanceNumber :: !Int
  , errors :: [Error]
  }

dupCheck
  :: ModuleName
  -> [(SourceLoc, Pre.Definition)]
  -> (HashMap QName (SourceLoc, Pre.Definition), [Error])
dupCheck mname = second errors . flip runState (DupState 0 []) . foldM go mempty
  where
    go defs (loc, def) = do
      name <- case def of
        Pre.ConstantDefinition d -> return $ Pre.definitionName d
        Pre.DataDefinition _ n _ _ -> return n
        Pre.ClassDefinition n _ _ -> return n
        Pre.InstanceDefinition typ _ -> do
          i <- gets instanceNumber
          modify' $ \s -> s { instanceNumber = instanceNumber s + 1 }
          return $ "instance-" <> shower i <> instanceNameEnding (shower $ pretty typ)
      let qname = QName mname name
      if HashMap.member qname defs then do
        let
          (prevLoc, _) = defs HashMap.! qname
          err = TypeError
            "Duplicate definition"
            (Just loc)
            $ PP.vcat
              [ "Previous definition at " <> pretty prevLoc
              , pretty prevLoc
              ]
        modify' $ \s -> s { errors = err : errors s }
        return defs
      else return $ HashMap.insert qname (loc, def) defs
      where
        instanceNameEnding n
          | Text.all (\b -> isAlphaNum b || isSpace b) n = fromText $ "-" <> Text.map replaceSpace n
          | otherwise = ""
        replaceSpace ' ' = '-'
        replaceSpace c = c
