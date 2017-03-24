{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Language.Prolog where

import                       Control.Monad
import                       Control.Applicative
import                       Data.Maybe
import                       Data.Monoid
import                       Data.List
import                       Data.Char
import qualified Data.Map as Map
import qualified Data.Set as Set
import                       Data.Foldable

type Name = String

newtype Var = Var Name deriving (Eq, Ord)

instance Show Var where
    show (Var s) = s

newtype Atom = Atom Name deriving (Eq, Ord)

instance Show Atom where
    show (Atom s) | maybe True (not . isLower) $ listToMaybe s = '\'':s ++ "'"
                  | otherwise                                       = s

data Expr = ExpVar Var
          | ExpAtom Atom
          | ExpFunc Atom [Expr]
            deriving (Eq)

instance Show Expr where
    show (ExpVar v) = show v
    show (ExpAtom a) = show a
    show (ExpFunc f xs) = show f ++ '(' : (concat $ intersperse "," $ fmap show xs) ++ ")"

newtype Subst = Subst {unSubst :: Map.Map Var Expr} deriving Eq

instance Show Subst where
    show (Subst s) = show $ maybe true id $ Map.foldrWithKey buildExpr Nothing s
        where buildExpr v r Nothing = Just $ ExpFunc (Atom "=") [ExpVar v, r]
              buildExpr v r (Just e) = Just $ ExpFunc (Atom ",") [(ExpFunc (Atom "=") [ExpVar v, r]), e]

instance Monoid Subst where
    mempty = Subst Map.empty
    mappend (Subst s1) (Subst s2) = Subst $ Map.fromList $ fmap (\x -> (x, substitute (Subst s2) (apply (Subst s1) x))) $ toList $ Set.union (Map.keysSet s1) (Map.keysSet s2)

singleton :: Var -> Expr -> Subst
singleton = (Subst.) . Map.singleton

apply :: Subst -> Var -> Expr
apply (Subst m) v = Map.findWithDefault (ExpVar v) v m

substitute :: Subst -> Expr -> Expr
substitute f (ExpVar v) = apply f v
substitute f a@(ExpAtom _) = a
substitute f (ExpFunc h xs) = ExpFunc h $ fmap (substitute f) xs

vars :: Expr -> Set.Set Var
vars (ExpVar v) = Set.singleton v
vars (ExpAtom _) = mempty
vars (ExpFunc _ xs) = foldMap vars xs

collectVars :: Subst -> Set.Set Var
collectVars (Subst s) = Map.foldrWithKey (\v e a -> a <> Set.singleton v <> vars e) mempty s

renameAll :: Set.Set Var -> Set.Set Var -> Subst
renameAll forbidden used = snd $ foldl f (forbidden <> used, mempty) used
        where f (forbidden, subst) v@(Var name) = let v' = head $ filter (`Set.notMember` forbidden) $ map (\n -> Var ('_':name ++ show n)) [1..] in (Set.insert v' forbidden, singleton v (ExpVar v') <> subst)

filterToRelevant :: Set.Set Var -> Subst -> Subst
filterToRelevant used (Subst subst) | null used = mempty
                                    | otherwise = let subst' = Map.filterWithKey (\k _ -> k `Set.member` used) subst in Subst $ subst' <> unSubst (filterToRelevant (Set.difference (collectVars $ Subst subst') used) (Subst subst))

unify :: Expr -> Expr -> Maybe (Expr, Subst)
unify (ExpAtom a) (ExpAtom b)   | a == b = Just (ExpAtom a, mempty)
                                | otherwise = Nothing
unify (ExpVar x) (ExpVar y)     | x == y = Just (ExpVar x, mempty)
                                | otherwise = Just (ExpVar x, singleton y (ExpVar x))
unify (ExpVar x) y              = Just (y, singleton x y)
unify x          (ExpVar y)     = Just (x, singleton y x)
unify (ExpFunc _ _) (ExpAtom _) = Nothing
unify (ExpAtom _) (ExpFunc _ _) = Nothing
unify x@(ExpFunc fx xs) y@(ExpFunc fy ys) | fx /= fy || length xs /= length ys = Nothing
                                          | otherwise = unifyAll xs ys >>= \s -> Just (substitute s x, s)
                                where unifyAll [] [] = Just mempty
                                      unifyAll (x:xs) (y:ys) = do
                                                    (_,s1) <- unify x y
                                                    (sr) <- unifyAll (fmap (substitute s1) xs) (fmap (substitute s1) ys)
                                                    return (s1 <> sr)

true :: Expr
true = ExpAtom $ Atom "true"

data Predicate = Fact {prdName :: Atom}
               | Predicate {prdName :: Atom, prdHead :: [Expr], prdGoal :: Expr}
                deriving Eq

instance Show Predicate where
    show (Fact name) = show name ++ "."
    show (Predicate name head goal) | goal == true = show (ExpFunc name head) ++ "."
                                    | otherwise = show (ExpFunc name head) ++ " :- " ++ show goal ++ "."

type Database = [Predicate]

newtype Proof a = Proof {runProof :: [a]} deriving (Show, Eq, Ord, Functor, Applicative, Monad, MonadPlus, Alternative)  -- ToDo: add State (Database), cuts…

match :: Database -> Set.Set Var -> Expr -> [(Subst, Expr)]
match dtb _ (ExpAtom name) = do
        (Fact name') <- dtb
        guard (name == name')
        return (mempty, true)
match dtb usedVars f = do
        (Predicate name head goal) <- dtb
        let ren = renameAll (usedVars <> vars f) ((foldMap vars head) <> (vars goal))
        (_, subst) <- maybe mzero return $ unify f $ ExpFunc name $ fmap (substitute ren) head
        return (subst, substitute (ren <> subst) goal)


fromList :: (MonadPlus m) => [a] -> m a
fromList = msum . fmap return

prove :: Database -> Expr -> [Subst]
prove dtb goal = fmap (filterToRelevant (vars goal)) $ runProof $ prove' dtb mempty goal

prove' :: Database -> Set.Set Var -> Expr -> Proof Subst
prove' dtb usedVars (ExpAtom (Atom "true")) = return mempty
prove' dtb usedVars (ExpAtom (Atom "fail")) = mzero
prove' dtb usedVars (ExpFunc (Atom ",") [goal1, goal2]) = do
                         subst <- prove' dtb (usedVars <> vars goal2) goal1
                         fmap (subst <>) $ prove' dtb (usedVars <> vars goal1 <> collectVars subst) $ substitute subst goal2
prove' dtb usedVars (ExpFunc (Atom ";") [goal1, goal2]) = prove' dtb (usedVars <> vars goal2) goal1 <|> prove' dtb (usedVars <> vars goal1) goal2
prove' dtb usedVars (ExpFunc (Atom "=") [lhs, rhs]) = maybe mzero return $ fmap snd $ unify lhs rhs
prove' dtb usedVars (ExpFunc (Atom "==") [lhs, rhs]) = if lhs == rhs then return mempty else mzero
prove' dtb usedVars (ExpVar (Var name)) = return $ singleton (Var name) true
prove' dtb usedVars expr = do
            (subst1, goal) <- fromList $ match dtb usedVars expr
            subst2 <- prove' dtb (usedVars <> collectVars subst1) goal
            return (subst1 <> subst2)
