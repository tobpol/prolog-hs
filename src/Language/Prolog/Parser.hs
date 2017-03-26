module Language.Prolog.Parser where

import Language.Prolog

import Text.Parsec
import Text.Parsec.Expr

import Data.Functor.Identity

parseDB = runParser (many predicate >>= \dtb -> eof >> return dtb) ()

parseQuery = runParser (exprOrInfx >>= \q -> string "." >> eof >> return q) () ""

predicate = try (atom >>= \name -> char '.' >> spaces >> return (Fact name)) <|> try simplePredicate <|> try complexPredicate
            where simplePredicate = do
                        ExpFunc name head <- func
                        spaces
                        char '.'
                        spaces
                        return $ Predicate name head true
                  complexPredicate = do
                        ExpFunc name head <- func
                        spaces
                        string ":-"
                        spaces
                        goal <- exprOrInfx
                        spaces
                        char '.'
                        spaces
                        return $ Predicate name head goal

expr :: ParsecT String () Identity Expr
expr = try func <|> try (fmap ExpAtom atom) <|> try (fmap ExpVar var) <|> parens exprOrInfx


infixOp :: String -> Assoc -> Operator String () Identity Expr
infixOp name = Infix (spaces >> string name >> spaces >> return (\x y -> ExpFunc (Atom name) [x,y]))

prefixOp :: String -> Operator String () Identity Expr
prefixOp name = Prefix (string name >> spaces >> return (\x -> ExpFunc (Atom name) [x]))

operatorTable = reverse [[infixOp "-->" AssocNone, infixOp ":-" AssocNone],
                 [prefixOp ":-", prefixOp "?-"],
                 [infixOp ";" AssocLeft, infixOp "|" AssocLeft],
                 [infixOp "->" AssocLeft, infixOp "*->" AssocLeft],
                 [infixOp "," AssocLeft],
                 [prefixOp "\\+"],
                 [prefixOp "~"],
                 fmap (\x -> infixOp x AssocNone) ["<", "=", "=..", "=@=", "=:=", "=<", "==", "=\\=", ">", ">=", "@<", "@=<", "@>", "@>=", "\\=", "\\==", "is"],
                 [infixOp ":" AssocLeft],
                 fmap (\x -> infixOp x AssocRight) ["+", "-", "/\\", "\\/", "xor"] ++ [prefixOp "?"],
                 fmap (\x -> infixOp x AssocRight) ["*", "/", "//", "rdiv", "<<", ">>", "mod", "rem"],
                 [infixOp "**" AssocNone, infixOp "^" AssocLeft, prefixOp "+", prefixOp "-", prefixOp "\\"]]
                 

exprOrInfx = try infx <|> expr
            where infx = buildExpressionParser operatorTable expr
                  {-infx = do
                    e1 <- expr
                    spaces
                    delimiter <- choice infixes
                    spaces
                    e2 <- exprOrInfx
                    return $ ExpFunc (Atom delimiter) [e1, e2]
                  infixes = fmap string [","] --TODO: support more, like [",", ";", "=", "==", "=..", "/=", "/==", "+", "-", "*", "/"]
-}

parens = between (char '(') (char ')')

func = do
    name <- atom
    xs <- parens $ sepBy expr $ char ',' >> spaces
    spaces
    return $ ExpFunc name xs

atom = try lowercaseName <|> try quotedName <|> specialName
        where lowercaseName = do
                x <- lower
                xs <- many letter
                spaces
                return $ Atom $ x:xs
              quotedName = do
                name <- between (char '\'') (char '\'') $ many $ noneOf "'"
                spaces
                return $ Atom $ name
              specialName = do
                name <- try (string "!") <|> try (string "[]")
                return $ Atom $ name
var = do
    x <- upper <|> char '_'
    xs <- many alphaNum
    spaces
    return $ Var $ x:xs
