{-|
Module      : Idris.Core.Constraints
Description : Check universe constraints.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
module Idris.Core.Constraints ( ucheck ) where

import Idris.Core.TT ( TC(..), UExp(..), UConstraint(..), FC(..),
                       ConstraintFC(..), Err'(..) )

import Control.Applicative
import Control.Monad.State.Strict
import Data.List
import Data.Maybe
import qualified Data.Map.Strict as M
import qualified Data.Set as S

-- fgl
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.Query.DFS
import Data.Graph.Inductive.Query.SP
import Data.Tree
import Control.Monad.Writer


-- | Check that a list of universe constraints can be satisfied.
ucheck :: S.Set ConstraintFC -> TC ()
ucheck = void . solve 10 . S.toList


data ConstraintTy = Lt | Leq
    deriving (Eq, Show)

solve :: Int -> [ConstraintFC] -> TC (M.Map UExp Int)
solve maxUniverseLevel ucs = do
    let
        allUExp :: [UExp]
        allUExp = nub $ concat
            [ case c of
                ULT lhs rhs -> [lhs, rhs]
                ULE lhs rhs -> [lhs, rhs]
            | ConstraintFC c _ <- ucs
            ]

        toInt :: M.Map UExp Int
        toInt = M.fromList (zip allUExp [1..])

        fromInt :: M.Map Int UExp
        fromInt = M.fromList (zip [1..] allUExp)

        numEdges :: Int
        numEdges = length allUExp

        constraintGraph :: Gr () ConstraintTy
        constraintGraph = mkGraph
            (map (\ e -> (e, ()) ) [1..numEdges])
            [ case c of
                ULT lhs rhs -> (toInt M.! lhs, toInt M.! rhs, Lt )
                ULE lhs rhs -> (toInt M.! lhs, toInt M.! rhs, Leq)
            | ConstraintFC c _ <- ucs
            ]

    let
        go :: [Node] -> M.Map UExp Int -> TC (M.Map UExp Int)
        go [] assignments = return assignments
        go (node:next) assignments = do
            let befores = inn constraintGraph node
            (values, othernodes) <- runWriterT $ forM befores $ \ (bef, _, ckind) -> do
                let befUExp = fromInt M.! bef
                let befValue = case (befUExp, M.lookup befUExp assignments) of
                                (UVal v, _) -> Just v
                                (_, Just v) -> Just v
                                _           -> Nothing
                case befValue of
                    Just v -> return (case ckind of Lt -> v+1 ; Leq -> v)
                    Nothing -> do
                        -- a universe value was not assigned to the "bef" node so far.
                        -- we know that: bef < node
                        -- or      that: bef <= node
                        case ckind of
                            Lt -> lift $ Error $ Msg $ unlines
                                [ "this is a Lt, failing"
                                , show bef
                                , show ckind
                                , show node
                                ]
                            Leq -> do
                                -- bef <= node
                                -- if "node <= bef": it's OK, assign both to whatever value "node" would get
                                -- if "node < bef" : error
                                -- otherwise       :
                                let
                                    -- check if nodeA < nodeB
                                    isLt :: [Node] -> Node -> Node -> Bool
                                    isLt visited nodeA nodeB | nodeA `elem` (nodeB:visited) = False
                                    isLt visited nodeA nodeB =
                                        if hasLEdge constraintGraph (nodeA, nodeB, Lt)
                                            then True
                                            else or $ [ isLt (nodeA:visited) next nodeB
                                                      | (_, next, Leq) <- out constraintGraph nodeA
                                                      ] ++
                                                      [ isConnected next nodeB
                                                      | (_, next, Lt) <- out constraintGraph nodeA
                                                      ]

                                    isConnected :: Node -> Node -> Bool
                                    isConnected nodeA nodeB = nodeB `elem` (nodeA : reachable nodeA constraintGraph)

                                if isLt [] node bef
                                    then lift $ Error $ Msg $ unlines
                                        [ "this is a Leq, that is not allowed."
                                        , show bef
                                        , show ckind
                                        , show node
                                        ]
                                    else do
                                        tell [befUExp]
                                        return 1

            let newValue = maximum (0:values)
            let assignments' = M.unionWith max assignments $ M.fromList $ (fromInt M.! node, newValue)
                                                                        : [ (n, newValue) | n <- othernodes ]
            go next assignments'

    go (topsort constraintGraph) M.empty
