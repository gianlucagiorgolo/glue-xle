-- Interface to XLE using the file polling strategy
-- The interface starts up XLE, loads a grammar and waits for input (sentences to be parsed?)

module Main where

import Data.List

import System.IO
import System.Directory
import System.Process
import System.Environment

import Control.Concurrent

import Parsers
import Sigma
import DataStructures
import XML
import DataTypes
import TP
import Txt

data Env = Env { statusFile :: (FilePath, Handle)
               , commandFile :: (FilePath, Handle)
               , xlerc :: (FilePath, Handle)
               , grammar :: FilePath
               , xmlOutputFile :: FilePath
               , xleStdin :: Handle
               , xleHandle :: ProcessHandle
               , lexicon :: Lexicon }

main = do
     grammar <- getGrammar
     grammar <- canonicalizePath grammar
     env <- createEnv grammar
     env <- startXLE env
     mainLoop env

getGrammar = do
     getArgs >>= return . head

createEnv grammar = do
     tmpDir <- getTemporaryDirectory
     sFile <- openTempFile tmpDir "status_file"
     cFile <- openTempFile tmpDir "command_file"
     xlerc <- openTempFile tmpDir "xlerc"
     (xmlOut,xmlOut_h) <- openTempFile tmpDir "xml_output"
     hClose xmlOut_h
     (gram,gram_h) <- openTempFile tmpDir "gram_file"
     gram <- canonicalizePath gram
     grammar_contents <- readFile grammar
     (grammar_contents,lex) <- return $ reconstructLexicon $ splitLexicon grammar_contents
     hPutStrLn gram_h grammar_contents
     hFlush gram_h
     -- setting the buffering properties
     hSetBuffering (snd $ sFile) NoBuffering
     hSetBuffering (snd $ cFile) NoBuffering
     env <- return $ Env { statusFile = sFile, commandFile = cFile, xleStdin = undefined, xleHandle = undefined, xlerc = xlerc, grammar = gram, lexicon = lex, xmlOutputFile = xmlOut}
     hPutStr (snd xlerc) ("create-parser " ++ gram ++ "\npoll " ++ (fst sFile) ++ " " ++ (fst cFile) ++ "\n")
     hFlush (snd xlerc)
     writeStatus env "0\n"
     return env

startXLE env = do
     (Just hin, _, _, handle) <- createProcess (proc "xle" [(fst $ xlerc env)]) {std_in = CreatePipe, std_out=CreatePipe, std_err=CreatePipe}
     return env{xleStdin = hin, xleHandle = handle}

-- loadGrammar grammar env = do
--      gFilename <- canonicalizePath grammar
--      writeCommand env ("create-parser " ++ gFilename ++ "\n")
--      writeStatus env '1'
--      waitUntilStatusEq env '0'

-- placeXLEInPollingMode env = do
--      hPutStr (xleStdin env) ("poll " ++ (fst $ statusFile env) ++ " " ++ (fst $ commandFile env) ++ "\n")
--      hFlush (xleStdin env)

data Command = Parse String | Quit

mainLoop env = do
     command <- getCommand env
     case command of
        Quit -> do waitUntilStatusEq env '0'
                   writeCommand env "exit\n"
                   writeStatus env "1\n"
                   waitForProcess (xleHandle env)
                   return ()
        Parse cmd -> do waitUntilStatusEq env '0'
                        writeCommand env cmd
                        writeStatus env "1\n"
                        waitUntilStatusEq env '0'
                        parses <- parseXMLOutput (xmlOutputFile env)
                        mapM (semanticProcessing env) parses
                        mainLoop env

semanticProcessing env cf_structs = do
     pools <- return $ createResourcePool cf_structs (lexicon env)   
     mapM_ (\(i,p) -> putStrLn ("Readings for pool " ++ show i) >> printProofsWithConstants p) $ zip [1..] pools

printProofsWithConstants :: ([(LambdaTerm,Formula)],Formula) -> IO ()
printProofsWithConstants s = do
  ps <- return $ (evaluateState (toDecoratedWithConstants s >>= \(ds,m) -> proofs ds >>= \p -> return $ replaceWithConstants p m) startState)
  pproofs ps  

pproofs :: [DataTypes.BinTree DecoratedSequent] -> IO ()
pproofs ps = do
  ps <- return $ map sanitizeVars ps
  ps <- return $ nubBy (\x y -> equivalentDecoratedSequent (getVal x) (getVal y)) ps
  case ps of
    [] -> putStrLn "Not a theorem"
    _ -> mapM_ printReading ps                     

printReading :: DataTypes.BinTree DecoratedSequent -> IO ()
printReading = putStrLn . lambda2text . betaReduce . monadReduce . etaReduce . term . snd . getVal

getCommand env = do 
     putStr ">>> "
     hFlush stdout
     line <- getLine
     case line of
        ":quit" -> return Quit
        _ -> return $ Parse $ "packed-xml-fs {" ++ line ++ "} " ++ (xmlOutputFile env) ++ "\n"

chop = reverse . tail . reverse

waitUntilStatusEq env s = do
     hFlush (snd $ statusFile env)
     b <- hIsEOF (snd $ statusFile env)
     case b of
       True -> waitUntilStatusEq env s
       False -> do content <- hLookAhead (snd $ statusFile env)
                   if content == s then return () else waitUntilStatusEq env s

ioPrint m = m >>= \x -> print x

writeCommand env cmd = cleanAndWrite (snd $ commandFile env) cmd

writeStatus env s = cleanAndWrite (snd $ statusFile env) s

cleanAndWrite :: Handle -> String -> IO ()
cleanAndWrite hdl s = do
     hSetFileSize hdl 0
     hPutStr hdl s
     hFlush hdl
     hSeek hdl AbsoluteSeek 0
