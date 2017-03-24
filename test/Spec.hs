import Language.Prolog
import Language.Prolog.Parser
import Test.Hspec

import Text.Parsec
import Control.Monad
import Data.Monoid

main :: IO ()
main = hspec $ do
    describe "Substitutions" $ do
        it "apply" $ do
            substitute (singleton (Var "X") (ExpAtom (Atom "a"))) (ExpFunc (Atom "f") [ExpVar (Var "X")]) `shouldBe` (ExpFunc (Atom "f") [ExpAtom (Atom "a")])
        it "compose" $ do
            (singleton (Var "X") (ExpVar (Var "Y")) <> singleton (Var "Y") (ExpAtom (Atom "a"))) `shouldBe` (singleton (Var "X") (ExpAtom (Atom "a")) <> singleton (Var "Y") (ExpAtom (Atom "a")))
            (singleton (Var "X") (ExpAtom (Atom "a")) <> singleton (Var "Y") (ExpAtom (Atom "b"))) `shouldBe` (singleton (Var "Y") (ExpAtom (Atom "b")) <> singleton (Var "X") (ExpAtom (Atom "a")))
    describe "Unification" $ do
        it "unifies two equal atoms" $ do
            unify (ExpAtom (Atom "a")) (ExpAtom (Atom "a")) `shouldBe` (Just (ExpAtom (Atom "a"), mempty))
        it "fails to unify differing atoms" $ do
            unify (ExpAtom (Atom "a")) (ExpAtom (Atom "b")) `shouldBe` Nothing
        it "binds a variable to a term" $ do
            unify (ExpVar (Var "X")) (ExpAtom (Atom "a")) `shouldBe` Just (ExpAtom (Atom "a"), singleton (Var "X") (ExpAtom (Atom "a")))
        it "unifies functors recursively" $ do
            let a  = ExpAtom (Atom "a")
            let fx = ExpFunc (Atom "test") [ExpVar (Var "X"), ExpVar (Var "Y")]
            let fy = ExpFunc (Atom "test") [ExpVar (Var "Y"), a]
            let un = ExpFunc (Atom "test") [a, a]
            unify fx fy `shouldBe` Just (un, singleton (Var "X") a <> singleton (Var "Y") a)
    describe "Database" $ do
        let true = ExpAtom $ Atom "true"
        let testDB = [Fact (Atom "test"),
                       Predicate (Atom "equal") [ExpVar (Var "X"), ExpVar (Var "X")] true]
        it "matches facts" $ do
            match testDB mempty (ExpAtom (Atom "test")) `shouldBe` (return (mempty, true))
        it "matches simple predicates" $ do
            match testDB mempty (ExpFunc (Atom "equal") [ExpVar (Var "Y"), ExpAtom (Atom "a")]) `shouldBe` (return ((singleton (Var "Y") (ExpAtom (Atom "a")) <> singleton (Var "_X1") (ExpAtom (Atom "a"))), true))
        it "renames variables in predicates" $ do
            match testDB mempty (ExpFunc (Atom "equal") [ExpVar (Var "X"), ExpAtom (Atom "a")]) `shouldNotBe` (return (singleton (Var "X") (ExpAtom (Atom "a")), true))
    describe "Proover" $ do
        let true = ExpAtom $ Atom "true"
        let false = ExpAtom $ Atom "false"
        let testDB = [Fact (Atom "test"),
                       Predicate (Atom "equal") [ExpVar (Var "X"), ExpVar (Var "X")] true]
        it "proves truth" $ do
            prove testDB true `shouldBe` return mempty
        it "fails to prove falsehood" $ do
            prove testDB false `shouldBe` mzero
        it "proves composite goals" $ do
            prove testDB (ExpFunc (Atom ",") [true, true]) `shouldBe` return mempty
            prove testDB (ExpFunc (Atom ";") [false, true]) `shouldBe` return mempty
    parser

parser = do 
    describe "Parser" $ do
        it "parses atoms" $ do
            parse atom "" "test" `shouldBe` Right (Atom "test")
            parse atom "" "'test'" `shouldBe` Right (Atom "test")
        it "parses variables" $ do
            parse var "" "X" `shouldBe` Right (Var "X")
            parse var "" "_y" `shouldBe` Right (Var "_y")
        it "parses expressions" $ do
            parse expr "" "test" `shouldBe` Right (ExpAtom $ Atom "test")
            parse expr "" "Test" `shouldBe` Right (ExpVar $ Var "Test")
            parse expr "" "test(a,X)" `shouldBe` Right (ExpFunc (Atom "test") [ExpAtom (Atom "a"), ExpVar (Var "X")])
        it "parses infix functors" $ do
            parse (exprOrInfx >>= \x -> eof >> return x) "" "a, b" `shouldBe` Right (ExpFunc (Atom ",") [ExpAtom (Atom "a"), ExpAtom (Atom "b")])
            parse (exprOrInfx >>= \x -> eof >> return x) "" "a, b; c" `shouldBe` Right (ExpFunc (Atom ";") [ExpFunc (Atom ",") [ExpAtom (Atom "a"), ExpAtom (Atom "b")], ExpAtom (Atom "c")])
        it "parses facts" $ do
            parse predicate "" "test." `shouldBe` Right (Fact $ Atom "test")
        it "parses predicates" $ do
            let equal = Predicate (Atom "equal") [ExpVar (Var "X"), ExpVar (Var "X")] true
            parse predicate "" "equal(X, X) :- true." `shouldBe` Right equal
            parse predicate "" "equal(X, X)." `shouldBe` Right equal
