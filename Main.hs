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
import qualified Data.Vector as V
import System.Environment

import Annotation
import qualified Desugar
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
    deps   = M.map (bifoldMap toSet toSet) p
    sorted = fmap (\n -> let (e, t) = p M.! n in (n, e, t)) <$> topoSort deps

    tcGroup tls = do
      let abstractedScopes = recursiveAbstract [(n, e) | (n, e, _) <- tls]
          abstractedTypes  = recursiveAbstract [(n, t) | (n, _, t) <- tls]
          abstractedTls    = [(f n, fmap B s, fmap B t)
                             | ((s, t), (n, _, _))
                               <- zip (zip abstractedScopes abstractedTypes) tls]
      checkedTls <- checkRecursiveDefs $ V.fromList abstractedTls
      let vf  = traverse (unvar return $ const $ throwError "inferProgram")
      checkedTls'  <- traverse (bitraverse vf vf) checkedTls
      let checkedTls'' = bimap (fmap B) (fmap B) <$> checkedTls'
      reledTls   <- Relevance.checkRecursiveDefs checkedTls''
      let names   = V.fromList [n | (n, _, _) <- tls]
          vf'     = bitraverseScope Relevance.fromMetaAnnotation
                               (unvar return $ const $ throwError "inferProgram'")
      reledTls' <- traverse (bitraverse vf' vf') $ V.map (\(e, t, r) -> (r, e, t)) reledTls
      reledTls'' <- traverse (traverse Relevance.fromRelevanceM) $ V.map (\(r, e, t) -> ((e, t), r)) reledTls'
      let instTls = HM.fromList
            [(names V.! i, ( instantiate (return . (names V.!)) e
                           , instantiate (return . (names V.!)) t
                           , Annotation r Explicit
                           ))
            | (i, ((e, t), r)) <- zip [0..] $ V.toList reledTls''
            ]
      addContext instTls

test :: FilePath -> IO ()
test inp = do
  mp <- fmap Desugar.program <$> Parser.parseFromFile Parser.program inp
  case mp of
    Nothing         -> return ()
    Just (Left err) -> putStrLn err
    Just (Right p)  -> case runTCM (inferProgram p (Hint . Just) >> gets tcContext) of
      (Left err, tr) -> do mapM_ putStrLn tr; putStrLn err
      (Right res, _) -> print $ (show . pretty) <$> res

main :: IO ()
main = do
  x:_ <- getArgs
  test x
{-
  case (infer . fmap (const undefined)) <$> Parser.parseString Parser.expr inp of
    Success (res, l) -> do
      putDoc $ pretty l
      putStrLn ""
      putStrLn ""
      putDoc $ pretty (fmap (uncurry Relevance.test) res :: Either String (Core.Expr Relevance.Decoration String, Core.Expr Relevance.Decoration String))
      putStrLn ""
    Failure d        -> putDoc d
    -}
