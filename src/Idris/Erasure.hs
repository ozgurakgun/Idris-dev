{-# LANGUAGE PatternGuards #-}

module Idris.Erasure
    ( findUnusedArgs
    , findUsed
    ) where

import Idris.AbsSyntax
import Idris.Core.CaseTree
import Idris.Core.TT
import Idris.Core.Evaluate

import Debug.Trace

import Control.Applicative
import Control.Monad.State
import Data.Maybe
import Data.List
import qualified Data.Set as S
import qualified Data.IntSet as IS
import qualified Data.Map as M
import qualified Data.IntMap as IM
import Data.Set (Set)
import Data.IntSet (IntSet)
import Data.Map (Map)
import Data.IntMap (IntMap)

-- UseMap maps names to the set of used (reachable) argument positions.
type UseMap = Map Name IntSet

-- DepMap maps functions (only functions) to their Deps.
type DepMap = Map Name Deps

-- Deps of a function is a map from argument index
-- to all usages of the argument, including conditions
-- and which constructor fields the particular usage touched.
type Deps = IntMap (Set (Ctors, Cond))

-- "Condition" is the conjunction
-- of elementary assumptions along the path from the root.
-- Elementary assumption (f, i) means that "function f uses the argument i".
type Cond = Set (Name, Int)

-- "Ctors" is the set of pairs (ctor_name, arg_no) saying
-- which constructor fields have been accessed to obtain the variable.
type Ctors = Set (Name, Int)

-- Just a translation from name to argument number.
type VarMap = Map Name (Int, Ctors)

findUsed :: Context -> Ctxt CGInfo -> [Name] -> DepMap
findUsed ctx cg ns = M.fromList [(n, getDeps n) | n <- ns]
  where
    getDeps :: Name -> Deps
    getDeps n = case lookupDef n ctx of
        [def] -> getDepsDef def
        []    -> error $ "erasure checker: unknown name: " ++ show n
        _     -> error $ "erasure checker: ambiguous name: " ++ show n

    getDepsDef :: Def -> Deps
    getDepsDef (Function ty t) = error "a function encountered"  -- TODO
    getDepsDef (TyDecl   ty t) = IM.empty
    getDepsDef (Operator ty n f) = IM.empty
    getDepsDef (CaseOp ci ty tys def tot cdefs)
        = getDepsSC varMap S.empty S.empty sc
      where
        varMap = M.fromList [(v, (i, S.empty)) | (i,v) <- zip [0..] vars]
        (vars, sc) = cases_compiletime cdefs  -- TODO: or cases_runtime?

    getDepsSC :: VarMap -> Cond -> SC -> Deps
    getDepsSC vs cd  ImpossibleCase     = IM.empty
    getDepsSC vs cd (UnmatchedCase msg) = IM.empty
    getDepsSC vs cd (ProjCase t alt)    = getDepsAlt vs cd alt
    getDepsSC vs cd (STerm    t)        = getDepsTerm vs cd t
    getDepsSC vs cd (Case     n alts)   = unionMap (getDepsAlt vs cd cs) alts
      where
        cs = fromMaybe (error $ "nonpatvar in case: " ++ show n) (M.lookup n vs)

    getDepsAlt :: VarMap -> Cond -> (Int, Ctors) -> CaseAlt -> Deps
    getDepsAlt vs cd cs (FnCase n ns sc) = error "an FnCase encountered"  -- TODO: what's this?
    getDepsAlt vs cd cs (ConstCase c sc) = error "a ConstCase encountered"
    getDepsAlt vs cd cs (SucCase   n sc) = error "a SucCase encountered"
    getDepsAlt vs cd cs (DefaultCase sc) = error "a DefaultCase encountered"
    getDepsAlt vs cd (i, cs) (ConCase n cnt ns sc)
        = getDepsSC (vs' `M.union` vs) cd sc  -- left-biased union
      where
        vs' = M.fromList [(n, (i, S.insert (n,j) cs)) | (n,j) <- zip ns [0..]]

    getDepsTerm :: VarMap -> Cond -> Term -> Deps
    getDepsTerm vs cd t = IM.empty

{-
data TT n = P NameType n (TT n) -- ^ named references
          | V !Int -- ^ a resolved de Bruijn-indexed variable
          | Bind n !(Binder (TT n)) (TT n) -- ^ a binding
          | App !(TT n) (TT n) -- ^ function, function type, arg
          | Constant Const -- ^ constant
          | Proj (TT n) !Int -- ^ argument projection; runtime only
                             -- (-1) is a special case for 'subtract one from BI'
          | Erased -- ^ an erased term
          | Impossible -- ^ special case for totality checking
          | TType UExp -- ^ the type of types at some level
-}

    unions :: [Deps] -> Deps
    unions = IM.unionsWith S.union

    unionMap :: (a -> Deps) -> [a] -> Deps
    unionMap f = unions . map f

{-
buildDepGraph :: Context -> Ctxt CGInfo -> [Name] -> DepGraph
buildDepGraph ctx cg = unionMap (findDepsDef cg <*> getDef ctx)
  where
    union :: [DepGraph] -> DepGraph
    union = M.unionsWith $ M.unionWith S.union

    unionMap :: (a -> DepGraph) -> [a] -> DepGraph
    unionMap f = union . map f

    getDef :: Context -> Name -> Def
    getDef ctx n = case lookupDef n ctx of
        [def] -> def
        [] -> error $ "erasure checker: unknown name: " ++ show n  -- TODO: fix this
        _  -> error $ "erasure checker: ambiguous name: " ++ show n  -- TODO: fix this

    findDepsDef :: Ctxt CGInfo -> Name -> Def -> DepGraph
    findDepsDef cg fn (Function ty t  ) = M.empty
    findDepsDef cg fn (TyDecl   ty t  ) = M.empty
    findDepsDef cg fn (Operator ty n f) = M.empty
    --  ^- non-pattern-matching definitions don't contribute to dependencies
    
    findDepsDef cg fn (CaseOp ci ty tys def tot cdefs)
        -- the fst component is the list of pattern variables, which we don't use
        = findDepsSC cg fn M.empty (snd $ cases_compiletime cdefs)  -- TODO: or cases_runtime?

    findDepsSC :: Ctxt CGInfo -> Name -> PatvarMap -> SC -> DepGraph
    findDepsSC cg fn vars  ImpossibleCase     = M.empty
    findDepsSC cg fn vars (UnmatchedCase msg) = M.empty
    findDepsSC cg fn vars (Case     n alts)   = unionMap (findDepsAlt cg fn vars) alts
    findDepsSC cg fn vars (ProjCase t alt )   = findDepsAlt cg fn vars alt
    findDepsSC cg fn vars (STerm t) = findDepsTerm cg vars (fn, Retval) t

    findDepsAlt :: Ctxt CGInfo -> Name -> PatvarMap -> CaseAlt -> DepGraph
    findDepsAlt cg fn vars (FnCase n ns sc) = findDepsSC cg fn vars sc  -- TODO: what's this?
    findDepsAlt cg fn vars (ConstCase c sc) = findDepsSC cg fn vars sc
    findDepsAlt cg fn vars (SucCase n sc)   = findDepsSC cg fn (M.insert n (error "put S here") vars) sc  -- TODO
    findDepsAlt cg fn vars (DefaultCase sc) = findDepsSC cg fn vars sc
    findDepsAlt cg fn vars (ConCase n cnt ns sc) = findDepsSC cg fn (ns `u` vars) sc
      where
        -- constructor name `n' is passed implicitly
        u :: [Name] -> PatvarMap -> PatvarMap
        vs `u` pmap = M.fromList [(var, S.singleton (n, i)) | (i, var) <- zip [0..] vs] `M.union` pmap

    -- where do we introduce the dependency
    -- f x = x
    -- (f, Result) -> (f, 0) ?

    findDepsTerm :: Ctxt CGInfo -> PatvarMap -> (Name, Arg) -> Term -> DepGraph
    findDepsTerm cg vars (tn,ta) (P _ n _) = tn ~> ta ~> case M.lookup n vars of
        Just vs -> vs                      -- an existing patvar
        Nothing -> S.singleton (n, Retval) -- must be the return value of something from the context
    findDepsTerm cg vars (tn,ta) (Bind n (Let t v) body) = union
        [ findDepsTerm cg vars (tn,ta) (instantiate v body)
        , findDepsTerm cg vars (tn,ta) t
        ]
    findDepsTerm cg vars (tn,ta) (Bind n b body) = union
        [ findDepsTerm cg (M.delete n vars) (tn,ta) body
        , findDepsTerm cg vars (tn,ta) (binderTy b)
        ]

    infixr 3 ~>
    (~>) :: (Ord a) => a -> b -> Map a b
    (~>) = M.singleton

findUsed :: Context -> Ctxt CGInfo -> [Name] -> UseMap
findUsed ctx cg = unionMap $ findUsedDef cg . getDef ctx
  where
    unionMap :: (a -> UseMap) -> [a] -> UseMap
    unionMap f = M.unionsWith IS.union . map f

    getDef :: Context -> Name -> Def
    getDef ctx n = case lookupDef n ctx of
        [def] -> def
        [] -> error $ "erasure checker: unknown name: " ++ show n  -- TODO: fix this
        _  -> error $ "erasure checker: ambiguous name: " ++ show n  -- TODO: fix this

    findUsedDef :: Ctxt CGInfo -> Def -> UseMap
    findUsedDef cg (Function ty t  ) = M.empty
    findUsedDef cg (TyDecl   ty t  ) = M.empty
    findUsedDef cg (Operator ty n f) = M.empty
    --  ^- non-pattern-matching definitions don't contribute to usage of data
    
    findUsedDef cg (CaseOp ci ty def tot cdefs)
        -- the fst component is the list of pattern variables, which we don't use
        = findUsedSC cg M.empty (snd $ cases_compiletime cdefs)  -- TODO: or cases_runtime?

    findUsedSC :: Ctxt CGInfo -> PatvarMap -> SC -> UseMap
    findUsedSC cg vars  ImpossibleCase     = M.empty
    findUsedSC cg vars (UnmatchedCase msg) = M.empty
    findUsedSC cg vars (Case     n alts) = unionMap (findUsedAlt cg vars) alts
    findUsedSC cg vars (ProjCase t alt) = findUsedAlt cg vars alt
    findUsedSC cg vars (STerm t) = unionMap lookUp . S.toList $ findUsedTerm cg t
      where
        lookUp :: Name -> UseMap
        lookUp n = case M.lookup n vars of
            Just (cn, i) -> M.singleton cn (IS.singleton i)
            Nothing      -> M.empty

    findUsedAlt :: Ctxt CGInfo -> PatvarMap -> CaseAlt -> UseMap
    findUsedAlt cg vars (FnCase n ns sc) = findUsedSC cg vars sc  -- TODO: what's this?
    findUsedAlt cg vars (ConstCase c sc) = findUsedSC cg vars sc
    findUsedAlt cg vars (SucCase n sc) = findUsedSC cg (M.insert n (error "put S here") vars) sc  -- TODO
    findUsedAlt cg vars (DefaultCase sc) = findUsedSC cg vars sc
    findUsedAlt cg vars (ConCase n cnt ns sc) = findUsedSC cg (ns `u` vars) sc
      where
        u :: [Name] -> PatvarMap -> PatvarMap
        vs `u` pmap = M.fromList [(var, (n, i)) | (i, var) <- zip [0..] vs] `M.union` pmap

    -- Find used pattern variables in the given term.
    findUsedTerm :: Ctxt CGInfo -> Term -> Set Name
    findUsedTerm cg (P _ n _) = S.singleton n
    findUsedTerm cg (Bind n (Let t v) body) = S.unions
        [ findUsedTerm cg v
        , S.delete n $ findUsedTerm cg body
        , findUsedTerm cg t ]
    findUsedTerm cg (Bind n b t) = S.unions
        [ findUsedTerm cg (binderTy b)
        , S.delete n $ findUsedTerm cg t ]
    findUsedTerm cg (Proj t i) = findUsedTerm cg t
    findUsedTerm cg t@(App _ _) | (P _ n _, args) <- unApply t
        = let unused = case lookupCtxt n cg of
                [cgi] -> unusedpos cgi
                _     -> []
          in S.unions [findUsedTerm cg arg | (i,arg) <- zip [0..] args, i `notElem` unused]
    findUsedTerm cg _ = S.empty
-}
        
findUnusedArgs :: [Name] -> Idris ()
findUnusedArgs names = do
    cg <- idris_callgraph <$> getIState
    mapM_ (process cg) names
  where
    process :: Ctxt CGInfo -> Name -> Idris ()
    process cg n = case lookupCtxt n cg of
        [x] -> do
            let unused = traceUnused cg n x 
            logLvl 1 $ show n ++ " unused: " ++ show unused
            addToCG n $ x{ unusedpos = unused }
        _ -> return ()

    traceUnused :: Ctxt CGInfo -> Name -> CGInfo -> [Int]
    traceUnused cg n (CGInfo args calls _ usedns _)
        = findIndices (not . (`elem` fused)) args
      where
        fargs   = concatMap (getFargpos calls) (zip args [0..])
        recused = [n | (n, i, (g,j)) <- fargs, used cg [(n,i)] g j]
        fused   = nub $ usedns ++ recused
        
    used :: Ctxt CGInfo -> [(Name, Int)] -> Name -> Int -> Bool
    used cg path g j
        | (g, j) `elem` path = False -- cycle, never used on the way

        | [CGInfo args calls _ usedns _] <- lookupCtxt g cg
        , j < length args  -- not overapplied
        = let directuse = args!!j `elem` usedns
              garg      = getFargpos calls (args!!j, j)
              recused   = map getUsed garg
          in directuse || or recused
          -- used on any route from here, or not used recursively

        | otherwise = True
      where
        getUsed (argn, j, (g', j')) = used cg ((g,j):path) g' j'

    getFargpos :: [(Name, [[Name]])] -> (Name, Int) -> [(Name, Int, (Name, Int))]
    getFargpos calls (n, i) = concatMap (getCallArgpos n i) calls
      where
        getCallArgpos :: Name -> Int -> (Name, [[Name]]) -> [(Name, Int, (Name, Int))]
        getCallArgpos n i (g, args) = mapMaybe (getOne g) (zip [0..] args)
        
        getOne :: Name -> (Int, [Name]) -> Maybe (Name, Int, (Name, Int))
        getOne g (j, xs)
            | n `elem` xs = Just (n, i, (g, j))
            | otherwise   = Nothing
