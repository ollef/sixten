module Main where

import Bound
import Bound.Scope
import Bound.Var
import Control.Monad.State
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.Monoid
import qualified Data.Text.IO as Text
import qualified Data.Vector as V
import System.Environment

import Annotation
import qualified Core
import Data
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

inferProgram :: Input.Program Name -> TCM s ()
inferProgram p = mapM_ tcGroup sorted
  where
    deps   = HM.map (bifoldMap defNames toHashSet) p <> HM.fromList constructorMappings
    defNames (Input.DataDefinition d) = toHashSet (constructorNames d) <> toHashSet d
    defNames x = toHashSet x
    sorted = fmap (\n -> (n, bimap (>>>= instCon) (>>= instCon) $ p HM.! n))
           . filter (`HM.member` p) <$> topoSort deps
    -- TODO check for duplicate constructors
    constructorMappings = [ (c, HS.singleton n)
                          | (n, (Input.DataDefinition d, _)) <- HM.toList p
                          , c <- constructorNames d
                          ]
    constructors = HS.fromList $ map fst constructorMappings
    instCon v
      | v `HS.member` constructors = Input.Con v
      | otherwise = pure v

    tcGroup tls = do
      let abstractedScopes = Input.recursiveAbstractDefs [(n, d) | (n, (d, _)) <- tls]
          abstractedTypes = recursiveAbstract [(n, t) | (n, (_, t)) <- tls]
          abstractedTls = [ ( Hint $ Just n
                            , s >>>= unvar (pure . B) Input.Global
                            , t >>>= Input.Global
                            )
                          | ((s, t), (n, _))
                            <- zip (zip abstractedScopes abstractedTypes) tls]
      checkedTls <- checkRecursiveDefs $ V.fromList abstractedTls
      let vf = error "inferProgram"
          checkedTls' = bimap (fmap $ fmap vf) (fmap vf) <$> checkedTls
      reledTls <- Relevance.checkRecursiveDefs checkedTls'
      reledTls' <- traverse (bitraverse (Input.bitraverseDef   Relevance.fromMetaAnnotation (traverse vf))
                                        (bitraverseScope Relevance.fromMetaAnnotation vf)) $ V.map (\(d, t, r) -> (r, d, t)) reledTls
      reledTls'' <- traverse (traverse Relevance.fromRelevanceM) $ V.map (\(r, d, t) -> ((d, t), r)) reledTls'
      let names = V.fromList [n | (n, (_, _)) <- tls]
          instTls = HM.fromList
            [(names V.! i, ( Input.instantiateDef (Core.Global . (names V.!)) d
                           , instantiate (Core.Global . (names V.!)) t
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
    Just (Right p)  -> case runTCM (inferProgram p >> gets tcContext) of
      (Left err, tr) -> do mapM_ putStrLn tr; putStrLn err
      (Right res, _) -> do
        mapM_ print $ (show . pretty . (\(x, (y, z, a)) -> (x, (fe y, fe z, show a)))) <$> HM.toList res
        putStrLn "------------- erased ------------------"
        mapM_ print $ (show . pretty) <$> [(x, fe $ eraseDef e) | (x, (e, _, a)) <- HM.toList res, isRelevant a]
  where
    fe :: Functor f => f Empty -> f String
    fe = fmap fromEmpty

main :: IO ()
main = do
  x:_ <- getArgs
  test x
