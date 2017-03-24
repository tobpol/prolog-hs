module Main where

import Language.Prolog
import Language.Prolog.Parser

import Data.Monoid

import System.Environment
import System.Exit
import System.IO
import System.IO.Error
import System.Console.Haskeline

main = do
    args <- getArgs
    case args of
        [] -> putStrLn "please pass a database file" >> exitFailure
        [name] -> initializeDB name
        _ -> putStrLn "too many arguments" >> exitFailure

initializeDB name = do
    input <- readFile name
    let dtb = parseDB name input
    case dtb of
        Left parseError -> print parseError >> exitFailure
        Right dtb' -> run dtb'

run dtb = runInputT defaultSettings $ loop dtb

loop dtb = do
    readMaybe <- getInputLine "?- "
    case readMaybe of
        Nothing -> return ()
        Just read -> do
            let queryRaw = parseQuery read
            case queryRaw of
                Left parseError -> outputStrLn (show parseError) >> loop dtb
                Right query -> prooveAndPrintResults dtb query >> loop dtb
    
prooveAndPrintResults dtb query = do
    let res = proove dtb query
    printResults res

printResults [] = outputStrLn "false."
printResults (r:rs) = do
    c <- getInputChar (show r)
    case c of
        (Just ';') -> printResults rs
        (Just '.') -> return ()
        Nothing -> return ()
        _ -> printResults (r:rs)

