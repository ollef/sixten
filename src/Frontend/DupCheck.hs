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
import qualified Syntax.Pre.Unscoped as Unscoped
import Util

data DupState = DupState
  { instanceNumber :: !Int
  , errors :: [Error]
  }

dupCheck
  :: ModuleName
  -> [(SourceLoc, Unscoped.TopLevelDefinition)]
  -> (HashMap QName (SourceLoc, Unscoped.TopLevelDefinition), [Error])
dupCheck mname = second errors . flip runState (DupState 0 []) . foldM go mempty
  where
    go defs (loc, def) = do
      name <- case def of
        Unscoped.TopLevelDefinition d -> return $ Unscoped.definitionName d
        Unscoped.TopLevelDataDefinition n _ _ -> return n
        Unscoped.TopLevelClassDefinition n _ _ -> return n
        Unscoped.TopLevelInstanceDefinition typ _ -> do
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
