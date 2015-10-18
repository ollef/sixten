module Main where

import Bound
import Bound.Scope
import Bound.Var
import Control.Monad.Except
import Control.Monad.State
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Hashable
import qualified Data.HashMap.Strict as HM
import qualified Data.Map as M
import qualified Data.Text.IO as Text
import qualified Data.Vector as V
import System.Environment

import Annotation
import qualified Desugar
import Erasure
import Hint
import Infer
import qualified Relevance
import qualified Input
import qualified Parser
import Pretty
import Monad
import TopoSort
import Util

inferProgram :: (Hashable v, Ord v, Show v)
             => Input.Program v -> (v -> NameHint) -> TCM s v ()
inferProgram p f = mapM_ tcGroup sorted
  where
    -- TODO: Add constructors to dependencies
    deps   = M.map (bifoldMap toSet toSet) p
    sorted = fmap (\n -> (n, p M.! n)) <$> topoSort deps

    tcGroup tls = do
      let abstractedScopes = Input.recursiveAbstractDefs [(n, d) | (n, (d, _)) <- tls]
          abstractedTypes = recursiveAbstract [(n, t) | (n, (_, t)) <- tls]
          abstractedTls = [(f n, fmap (fmap B) s, fmap B t)
                          | ((s, t), (n, _))
                            <- zip (zip abstractedScopes abstractedTypes) tls]
      checkedTls <- checkRecursiveDefs $ V.fromList abstractedTls
      let vf = unvar return $ const $ throwError "inferProgram"
      checkedTls' <- traverse (bitraverse (traverse (traverse vf)) (traverse vf)) checkedTls
      let checkedTls'' = bimap (fmap (fmap B)) (fmap B) <$> checkedTls'
      reledTls <- Relevance.checkRecursiveDefs checkedTls''
      let names = V.fromList [n | (n, (_, _)) <- tls]
          vf' = unvar return $ const $ throwError "inferProgram'"
      reledTls' <- traverse (bitraverse (Input.bitraverseDef   Relevance.fromMetaAnnotation (traverse vf'))
                                        (bitraverseScope Relevance.fromMetaAnnotation vf')) $ V.map (\(d, t, r) -> (r, d, t)) reledTls
      reledTls'' <- traverse (traverse Relevance.fromRelevanceM) $ V.map (\(r, d, t) -> ((d, t), r)) reledTls'
      let instTls = HM.fromList
            [(names V.! i, ( Input.instantiateDef (pure . (names V.!)) d
                           , instantiate (pure . (names V.!)) t
                           , Annotation r Explicit
                           ))
            | (i, ((d, t), r)) <- zip [0..] $ V.toList reledTls''
            ]
      addContext instTls

test :: FilePath -> IO ()
test inp = do
  mp <- fmap Desugar.program <$> Parser.parseFromFile Parser.program inp
  case mp of
    Nothing         -> return ()
    Just (Left err) -> Text.putStrLn err
    Just (Right p)  -> case runTCM (inferProgram p (Hint . Just) >> gets tcContext) of
      (Left err, tr) -> do mapM_ putStrLn tr; putStrLn err
      (Right res, _) -> do
        mapM_ print $ (show . pretty . (\(x, (y, z, a)) -> (x, (y, z, show a)))) <$> HM.toList res
        putStrLn "------------- erased ------------------"
        -- mapM_ print $ (show . pretty) <$> [(x, erase e) | (x, (e, _, a)) <- HM.toList res, isRelevant a]

main :: IO ()
main = do
  x:_ <- getArgs
  test x
