module Parsers where

-- import Data.Char
import qualified Data.Map as Map
import Data.List.Split
import Control.Monad.State
import Data.Char

import DataStructures
import Text.Parsec
import Text.Parsec.Expr
import DataTypes



-- utils 

maybeBetween :: Stream s m t => ParsecT s u m open -> ParsecT s u m close -> ParsecT s u m a -> ParsecT s u m a
maybeBetween open close p = do
    o <- optionMaybe open
    case o of
       Nothing -> do
            a <- p
            return a
       Just _ -> do
            a <- p
            close
            return a

trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace

-- lambda stuff

data LambdaParserState = LambdaParserState { accumulator :: Int
                                           , varMap :: Map.Map String Int }

newState = LambdaParserState 0 Map.empty

parseLambdaTerm s = runParser (lambdaExprParser >>= \l -> eof >> return l) newState "" s

getVarId :: String -> Parsec String LambdaParserState Int
getVarId name = do
    s <- getState
    m <- return $ varMap s
    case Map.lookup name m of
       Nothing -> do
           i <- return $ accumulator s
           putState s{accumulator = i+1,varMap = Map.insert name i m}
           return i
       Just i -> return i

lambdaExprParser :: Parsec String LambdaParserState LambdaTerm
lambdaExprParser = do char '\\'
                      var <- lambdaVariable
                      spaces
                      string "->"
                      spaces
                      expr <- lambdaExprParser
                      return $ Lambda var expr
               <|> do char '<'
                      l <- lambdaExprParser
                      char ','
                      r <- lambdaExprParser
                      char '>'
                      return $ Pair l r
               <|> do string "1"
                      char '('
                      t <- lambdaExprParser
                      char ')'
                      return $ FirstProjection t
               <|> do string "2"
                      char '('
                      t <- lambdaExprParser
                      char ')'
                      return $ SecondProjection t
               <|> do string "&"
                      char '('
                      t <- lambdaExprParser
                      char ')'
                      return $ Eta t
               <|> (try $ do binds <- sepBy1 lambdaTerm (spaces >> string ":*:" >> spaces)
                             return $ foldl1 (:*:) binds)
               <|> do apps <- many1 (spaces >> lambdaTerm >>= \t -> spaces >> return t)
                      return $ foldl1 App apps

lambdaTerm :: Parsec String LambdaParserState LambdaTerm
lambdaTerm = lambdaVariable
         <|> lambdaConstant
         <|> do char '('
                expr <- lambdaExprParser      
                char ')'
                return expr

lambdaVariable = do
    c <- upper
    cs <- many alphaNum
    i <- getVarId $ c : cs
    return $ V i

lambdaConstant = do
    c <- lower
    cs <- many alphaNum
    return $ C $ c : cs

-- linear stuff

parseLinearTermTemplate s = parse (linearTermTemplate >>= \f -> eof >> return f) "" s

linearTermTemplate :: Parsec String () LinearTermTemplate
linearTermTemplate = buildExpressionParser table operand 

table = [[Prefix mon], [Infix tens AssocRight], [Infix impl AssocRight]] where
      mon = do
         spaces
         char '<'
         modality <- many alphaNum
         char '>'
         spaces
         return $ Diamond modality
      tens = spaces >> string "*" >> spaces >> return LinearTensor
      impl = spaces >> string "--o" >> spaces >> return LinearImplication

operand = p <|> atomic where
        p = do
          spaces
          char '['
          spaces
          l <- linearTermTemplate
          spaces
          char ']'
          spaces
          return l

atomic = do
    s <- sigmaConstraint 
    return $ Atomic s


sigmaConstraint :: Parsec String () SigmaConstraint
sigmaConstraint = (try variable) <|> (try sigmaProjection) <|> (try sigmaOutsideIn) <|> sigmaOutsideIn

subscript = char '_'
typeSeparator = char ':'

variable = do
     spaces
     h <- upper
     t <- many alphaNum
     typeSeparator
     ty <- many1 lower
     spaces
     return $ Variable (h : t) ty

sigmaProjection = do
     spaces
     fc <- fConstraint
     subscript
     char 's'
     typeSeparator
     t <- many1 lower
     spaces
     return $ SigmaProjection fc t

sigmaOutsideIn = do
     spaces
     char '('                      
     spaces
     fc <- fConstraint
     subscript
     char 's'
     many1 space
     feats <- features
     spaces 
     char ')'
     typeSeparator
     t <- many1 lower
     spaces
     return $ SigmaOutsideIn (SigmaProjection fc "") feats t

sigmaInsideOut = do
     spaces
     char '('                      
     spaces
     feats <- features
     many1 space
     fc <- fConstraint
     subscript
     char 's'    
     spaces 
     char ')'
     typeSeparator
     t <- many1 lower
     spaces
     return $ SigmaInsideOut feats (SigmaProjection fc "") t

fConstraint = up <|> down <|> path 

up = spaces >> char '^' >> spaces >> return Up

down = spaces >> char '!' >> spaces >> return Down

path = do 
     spaces
     char '('
     spaces
     c <- lookAhead anyChar
     case c of
       '^' -> do
          up
          feats <- features
          spaces
          char ')'
          spaces
          return $ FOutsideIn Up feats
       '!' -> do
          down
          feats <- features
          spaces
          char ')'
          spaces
          return $ FOutsideIn Down feats
       '(' -> do
          fc <- fConstraint
          feats <- features
          spaces
          char ')'
          spaces
          return $ FOutsideIn fc feats
       _ -> try set <|> normal where 
         normal = do
          spaces
          feats <- features
          fc <- fConstraint
          spaces
          char ')'
          spaces
          return $ FInsideOut feats fc -- feats fc
         set = do
          spaces
          feats <- features
          spaces
          char '$'
          spaces
          fc <- fConstraint
          spaces
          char ')'
          spaces
          return $ FInsideOutSet feats fc -- feats fc
           
feature = many1 alphaNum
features = sepEndBy1 feature (many1 space)

-- xml stuff

parseEquivalence e = fromRight $ parse equivalence "" e

fromRight (Right a) = a
fromRight (Left _) = undefined

equivalence :: Parsec String () [DataStructures.Context]
equivalence = do
    Parsers.or
    openPar
    es <- sepBy1 (equivalence <|> atom) comma
    closePar
    return $ concat es

or = spaces >> string "or" >> spaces
openPar = spaces >> char '(' >> spaces
closePar = spaces >> char ')' >> spaces
comma = spaces >> char ',' >> spaces
atom = do 
     spaces
     name <- many1 $ noneOf ",() \n\t\r"
     spaces
     return [name]

context :: Parsec String () [DataStructures.Context]
context = equivalence <|> atom
  
orlist = do
    Parsers.or
    openPar
    es <- sepBy1 atom comma
    closePar
    return $ concat es   

parseContext e = fromRight $ parse context "" e

-- Lexicon stuff


{-
data LexiconStates = AllTheRest | Lexicon

splitLexicon :: String -> (String,Lexicon)
splitLexicon lexicon = runState (aux AllTheRest lexicon) Map.empty where
      aux AllTheRest (' ' : 'L' : 'E' : 'X' : 'I' : 'C' : 'O' : 'N' : ' ' : rest) = do
        endOfHeader <- return $ takeWhile (/= '\n') rest
        rest <- return $ tail $ dropWhile (/= '\n') rest
        rest' <- aux Lexicon rest
        return $ " LEXICON " ++ endOfHeader ++ "\n" ++ rest'
      aux AllTheRest (c : rest) = aux AllTheRest rest >>= \rest' -> return $ c : rest'
      aux Lexicon ('-' : '-' : '-' : '-' : rest) = aux AllTheRest rest >>= \rest' -> return $ "----" ++ rest'
      aux Lexicon (c : rest) | isSpace c = aux Lexicon rest >>= \rest' -> return $ c : rest'
                             | otherwise = do
                                 definition <- return $ c : (takeWhile (/= '.') rest)
                                 rest <- return $ tail $ dropWhile (/= '.') rest
                                 word <- return $ takeWhile (not . isSpace) definition
                                 xle_stuff <- return $ takeWhile (/= '§') definition
                                 semantic_stuff <- return $ tail $ dropWhile (/= '§') definition
                                 (lambda : form_temp : _) <- return $ map trim $ splitOn "::" semantic_stuff
                                 lambda <- return $ case parseLambdaTerm lambda of
                                                         Left err -> error $ "Problem in parsing this definition (specifically the lambda term):\n" ++ definition ++ "\nParsec error: " ++ show err
                                                         Right l -> l
                                 form_temp <- return $ case parseLinearTermTemplate form_temp of
                                                         Left err -> error $ "Problem in parsing this definition (specifically the linear formula):\n" ++ definition ++ "\nParsec error: " ++ show err
                                                         Right f -> f
                                 lex <- get
                                 put $ Map.insert word [(lambda,form_temp)] lex
                                 rest' <- aux Lexicon rest
                                 return $ xle_stuff ++ "." ++ rest'
      aux _ [] = return ""  
-}

data Section = ConfigSec 
             | RulesSec
             | TemplatesSec
             | LexiconSec
             | SemanticTemplatesSec deriving (Eq, Ord, Show)

splitLexicon :: String -> Map.Map Section String
splitLexicon s = aux (lines s) Nothing Map.empty where
     aux [] _ m = m
     aux (l : rest) (Just sec) m | isSectionHeader l = aux rest (Just $ getSectionType l) (Map.insert (getSectionType l) l m)
                                 | otherwise = aux rest (Just sec) (Map.insertWith (\a b -> b ++ "\n" ++ a) sec l m)
     aux (l : rest) Nothing m | isSectionHeader l = aux rest (Just $ getSectionType l) (Map.insert (getSectionType l) l m) 
                              | otherwise = aux rest Nothing m -- useless space
     isSectionHeader l = length ws == 4 && elem (ws !! 2) ["CONFIG", "RULES", "LEXICON", "TEMPLATES", "SEMANTICTEMPLATES"] where
        ws = words l
     getSectionType l = let ws = words l
                        in case (ws !! 2) of
                             "CONFIG" -> ConfigSec
                             "RULES" -> RulesSec
                             "TEMPLATES" -> TemplatesSec
                             "LEXICON" -> LexiconSec
                             "SEMANTICTEMPLATES" -> SemanticTemplatesSec
                             _ -> undefined



reconstructLexicon :: Map.Map Section String -> (String,Lexicon)
reconstructLexicon m = (unlines [config,rules,templs,xlelex],lexicon) where
     config = Map.findWithDefault "" ConfigSec m
     rules = Map.findWithDefault "" RulesSec m
     templs = Map.findWithDefault "" TemplatesSec m
     (xlelex,lexicon) = createXLELexicon $ expandSemanticTemplates (Map.findWithDefault "" LexiconSec m) semTempls
     semTempls = createSemanticTemplates $ Map.findWithDefault "" SemanticTemplatesSec m

createXLELexicon :: String -> (String,Lexicon)
createXLELexicon s = runState (aux s) Map.empty where
      aux ('-' : '-' : '-' : '-' : rest) = aux rest >>= \rest' -> return $ "----" ++ rest'
      aux (c : rest) | isSpace c = aux rest >>= \rest' -> return $ c : rest'
                     | otherwise = let line = c : takeWhile (/= '\n') rest 
                                       headerBool = length (words line) == 4 && (words line) !! 2 == "LEXICON"
                                   in case headerBool of 
                                    True -> aux (tail $ dropWhile (/= '\n') rest) >>= \rest' -> return $ line ++ rest'
                                    False -> do
                                     definition <- return $ c : (takeWhile (/= '.') rest)
                                     rest <- return $ tail $ dropWhile (/= '.') rest
                                     word <- return $ takeWhile (not . isSpace) definition
                                     xle_stuff <- return $ takeWhile (/= '§') definition
                                     semantic_stuff <- return $ tail $ dropWhile (/= '§') definition
                                     (lambda : form_temp : _) <- return $ map trim $ splitOn "::" semantic_stuff
                                     lambda <- return $ case parseLambdaTerm lambda of
                                                         Left err -> error $ "Problem in parsing this definition (specifically the lambda term):\n" ++ definition ++ "\nParsec error: " ++ show err
                                                         Right l -> l
                                     form_temp <- return $ case parseLinearTermTemplate form_temp of
                                                            Left err -> error $ "Problem in parsing this definition (specifically the linear formula):\n" ++ definition ++ "\nParsec error: " ++ show err
                                                            Right f -> f
                                     lex <- get
                                     put $ Map.insert word [(lambda,form_temp)] lex
                                     rest' <- aux rest
                                     return $ xle_stuff ++ "." ++ rest'
      aux [] = return ""  

createSemanticTemplates :: String -> TemplateEnvironment
createSemanticTemplates s = aux s Map.empty where
   aux [] m = m
   aux ('-' : '-' : '-' : '-' : _) m = m
   aux (c : rest) m | isSpace c = aux rest m
                    | otherwise = aux rest' m' where
                       line = c : takeWhile (/= '\n') rest
                       headerBool = length (words line) == 4 && (words line) !! 2 == "SEMANTICTEMPLATES"
                       rest' = case headerBool of 
                                 False -> tail $ dropWhile (/= '.') rest
                                 True -> tail $ dropWhile (/= '\n') rest
                       def = (c : takeWhile (/= '.') rest) ++ "."
                       m' = case headerBool of
                                 True -> m
                                 False -> case runParser template [] "" def of
                                    Right x -> Map.insert (name x) x m
                                    Left _ -> error $ "Error in parsing template: " ++ def
                       
{-createSemanticTemplates s = aux (lines s) Map.empty where
    aux [] m = m                          
    aux ("----" : _) m = m
    aux (l : rest) m = aux rest m' where
       ws = words l
       m' = case length ws == 4 && (ws !! 2) == "SEMANTICTEMPLATES" of
               True -> m
               False -> case runParser template [] "" l of
                          Right x -> Map.insert (name x) x m
                          Left err -> error $ "Error in parsing template: " ++ l
-}
expandSemanticTemplates :: String -> TemplateEnvironment -> String
expandSemanticTemplates s te = aux s False where
       paux = many1 (try tempcall <|> anythingElse)
       anythingElse = many1 $ noneOf "@"
       tempcall = do
         tc <- templateCall
         return $ expandTemplateCall tc te
       aux [] _ = []
       aux ('.' : rest) _ = '.' : aux rest False
       aux ('§' : rest) _ = '§' : aux rest True
       aux (c : rest) False = c : aux rest False
       aux s True = let def = (takeWhile (/= '.')) s
                        rest = dropWhile (/= '.') s
                    in case parse paux "" def of
                        Right x -> concat x ++ aux rest True
                        Left _ -> error $ "Error when processing the lexicon: " ++ s



-- Templates

templateName :: Parsec String a Name
templateName = many1 alphaNum                                                               

templateArgument :: Parsec String a Argument
templateArgument = many1 alphaNum

template :: Parsec String [Argument] Template
template = do
    spaces
    name <- templateName
    spaces
    args <- arguments
    putState args -- we store the list of argument names
    spaces
    char '='
    raw <- many1 $ try templateSpacingToken <|> try templateStringToken <|> try templateSeparatorToken <|> (templateCall >>= \x -> return $ TemplateCallToken x)
    spaces
    char '.'
    return $ Template name args raw

spaceChars = " \r\t\n"
fullStopChars = "."
delimiterChars = "()[]\\{}"
templateCallChars = "@"
reservedChars = spaceChars ++ fullStopChars ++ delimiterChars ++ templateCallChars

templateSeparatorToken :: Parsec String a RawTemplateBody
templateSeparatorToken = do s <- many1 $ Text.Parsec.oneOf delimiterChars
                            return $ SeparatorToken s

templateStringToken :: Parsec String [Argument] RawTemplateBody
templateStringToken = do content <- many1 $ noneOf reservedChars
                         args <- getState
                         case elem content args of
                            True -> return $ ArgumentToken content
                            False -> return $ StringToken content

templateSpacingToken :: Parsec String a RawTemplateBody
templateSpacingToken = many1 space >>= \x -> return $ SpacingToken x

arguments :: Parsec String a [Argument]
arguments = (try list) <|> noArg where
      list = do
         spaces
         char '('
         args <- sepEndBy1 templateArgument (many1 space)
         char ')'
         return args
      noArg = return []

templateCall :: Parsec String a TemplateCall
templateCall = (try withParams) <|> withoutParams where
     withParams = do
      char '@'
      char '('
      name <- templateName
      many1 space
      args <- sepEndBy1 anythingElse (many1 space)
      char ')'
      spaces
      return $ TemplateCall name args
     withoutParams = do
      char '@'
      name <- templateName
      spaces
      return $ TemplateCall name []
     anythingElse = many1 $ noneOf reservedChars


--test

foo = do
  conts <- readFile "/Users/Ggiorgolo/work/haskell-xle-wrapper/test.lfg"
  (xle,lex) <- return $ reconstructLexicon $ splitLexicon conts
  putStrLn xle
  print lex

bar = do
  conts <- readFile "/Users/Ggiorgolo/work/haskell-xle-wrapper/test.lfg"
  print $ splitLexicon conts
