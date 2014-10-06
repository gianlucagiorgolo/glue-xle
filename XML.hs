module XML where

import Data.Maybe
import Text.XML.Light
import Data.Tree
import Data.List
import Data.List.Split
import Data.Char
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Monad
import Parsers hiding (trim)

import DataStructures

parseXMLOutput :: FilePath -> IO [(CStructure,FStructure)]
parseXMLOutput file = do
   contents <- readFile file
   dom <- return $ fromJust $ parseXMLDoc contents
   choiceTree <- return $ collectContexts dom

   cxtGroups <- return $ contextGroups choiceTree
   equivalenceMap <- return $ collectEquivalences dom
   concreteContexts <- return $ collectTerminals choiceTree
   contextMap <- return $ createContextMap concreteContexts cxtGroups
   cstructures <- return $ getCStructures dom concreteContexts contextMap equivalenceMap
   fstructures <- return $ getFStructures dom concreteContexts contextMap equivalenceMap
   return $ pair cstructures fstructures

   -- case choiceTree == no_context of
   --   False -> do
   --      cxtGroups <- return $ contextGroups choiceTree
   --      equivalenceMap <- return $ collectEquivalences dom
   --      concreteContexts <- return $ collectTerminals choiceTree
   --      contextMap <- return $ createContextMap concreteContexts cxtGroups
   --      cstructures <- return $ getCStructures dom concreteContexts contextMap equivalenceMap
   --      fstructures <- return $ getFStructures dom concreteContexts contextMap equivalenceMap
   --      return $ pair cstructures fstructures
   --   True -> do
   --      -- do something
   --      return undefined

pair :: Eq a => [(a,b)] -> [(a,c)] -> [(b,c)]
pair [] _ = []
pair ((a,b) : rest) cs = (b,unsafeLookup cs) : (pair rest) cs where
     unsafeLookup [] = error "Unsafe lookup in pair"    
     unsafeLookup ((a',c) : rest) | a == a' = c
                                  | otherwise = unsafeLookup rest

verify :: a -> Maybe a -> a
verify a Nothing = a
verify _ (Just a) = a         

safeHead :: a -> [a] -> a
safeHead a [] = a
safeHead _ (a : _) = a           

no_context :: ChoiceTree
no_context = Node "" []

trim :: String -> String
trim "" = ""
trim s = reverse $ dropWhile isSpace $ reverse $ dropWhile isSpace s

getContext el = fromJust $ findAttr (unqual "context") el
getContexts el = parseContext $ fromJust $ findAttr (unqual "context") el

collectTerminals :: Tree a -> [a]
collectTerminals (Node a []) = [a]
collectTerminals (Node _ children) = concat $ map collectTerminals children

createContextMap :: [Context] -> Set.Set (Set.Set Context) -> Map.Map Context (Set.Set Context)
createContextMap cxts equivs = aux cxts equivs Map.empty where
   aux [] _ m = m
   aux (c : cs) equivs m = aux cs equivs $ Map.insert c (Set.findMin $ Set.filter (Set.member c) equivs) m

collectContexts :: Element -> ChoiceTree
collectContexts dom = 
   case findElements (unqual "alternatives_for") dom of
        [] -> no_context
        (first : rest) -> construct_tree first_tree rest where
          construct_tree t [] = t
          construct_tree t (el : rest) = construct_tree (append (toTree el) t) rest
          first_tree = toTree first
          toTree el = Node cont children where
              cont = getContext el
              raw_children = strContent el
              children = map (\x -> Node (trim x) []) $ splitOn "," $ reverse $ tail $ reverse $ tail raw_children
          append t (Node a children) = 
            case (rootLabel t) == a of
              True -> t
              False -> Node a $ map (append t) children

contextGroups :: ChoiceTree -> Set.Set (Set.Set Context)
contextGroups t = aux t Set.empty where
    aux (Node c []) current = Set.singleton $ Set.insert c current
    aux (Node c children) current = 
        foldr Set.union Set.empty $ map (\x -> aux x (Set.insert c current)) children

collectEquivalences :: Element -> EquivalenceMap
collectEquivalences dom = 
    case findElements (unqual "definition_of") dom of
      [] -> Map.empty
      defs -> foldr aux Map.empty defs where
        aux el m = Map.insert cont equivs m where
          cont = getContext el
          equivs = parseEquivalence $ strContent el

getCStructures :: Element -> [Context] -> Map.Map Context (Set.Set Context) -> EquivalenceMap -> [(Context,CStructure)]
getCStructures dom concreteContexts contextMap equivalenceMap = do
     phiMappings <- return $ collectPhiMappings dom
     phiMappings <- return $ expandEquivalenceMap phiMappings equivalenceMap
     phiMappings <- return $ createPhiMapping phiMappings contextMap 
     subtrees <- return $ collectSubtrees dom
     subtrees <- return $ expandEquivalenceMap subtrees equivalenceMap
     guard ((not $ null subtrees) && (not $ Map.null phiMappings))
     roottree <- return $ head subtrees -- here I'm assuming that the first subtree is always the root...
     currentcontext <- concreteContexts
     phi <- return $ case Map.lookup currentcontext phiMappings of
                       Nothing -> error $ "Lookup error in trying to find the phi mapping for context " ++ currentcontext ++ " in phiMappings: " ++ show phiMappings
                       Just a -> a
     return (currentcontext,CStructure { tree = reconstructTree currentcontext roottree subtrees contextMap
                                       , phiMapping = Map.fromList phi}) 
               

expandEquivalenceMap:: [(Context,a)] -> EquivalenceMap -> [(Context,a)]
expandEquivalenceMap subs equivmap = Map.foldrWithKey aux subs equivmap where
       aux k cxts subs = foldr (\cxt subs -> foldr (\t subs -> subs ++ [(cxt,t)]) subs ts) subs cxts where
           ts = map snd $ filter (\(c,_) -> c == k) subs


reconstructTree :: Context -> (Context,BinTree (Id,Label)) -> [(Context,BinTree (Id,Label))] -> Map.Map Context (Set.Set Context) -> BinTree (Id,Label)
reconstructTree _ (_,t@(Terminal _)) _ _  = t
reconstructTree cxt (_,(Unary a (Terminal (id,_)))) subtrees contextMap  = Unary a t where
    t = reconstructTree cxt t' subtrees contextMap 
    t' = findSuitableTree cxt id subtrees contextMap 
reconstructTree cxt (_,(Binary (Terminal (l_id,_)) a (Terminal (r_id,_)))) subtrees contextMap  = Binary l a r where
    l = reconstructTree cxt l' subtrees contextMap 
    l' = findSuitableTree cxt l_id subtrees contextMap
    r = reconstructTree cxt r' subtrees contextMap 
    r' = findSuitableTree cxt r_id subtrees contextMap
reconstructTree _ _ _ _ = undefined

findSuitableTree :: Context -> Id -> [(Context,BinTree (Id,Label))] -> Map.Map Context (Set.Set Context) -> (Context,BinTree (Id,Label))
findSuitableTree cxt id subtrees contextMap = 
    let aux legalContexts [] = error $ "Error in findSuitableTree, current context " ++ cxt ++ ", looking for id " ++ show id ++ ", in subtrees " ++ show subtrees ++ ", allowing the following legal contexts " ++ show legalContexts
        aux legalContexts ((cxt,t) : rest) | Set.member cxt legalContexts && id == getId t = Just (cxt,t)
                                           | otherwise = aux legalContexts rest
        getId (Terminal (id,_)) = id
        getId (Unary (id,_) _) = id
        getId (Binary _ (id,_) _) = id
    in fromJust $ aux ((Map.!) contextMap cxt) subtrees

unknown_label = "UNKNOWN LABEL"

hasLabel :: Element -> String -> Bool
hasLabel el label = case findChild (unqual "label") el of
          Nothing -> False
          Just a -> strContent a == label

getArg :: String -> Element -> String
getArg n el = trim $ strContent $ head $ filterChildren p el where
         p el = elName el == (unqual "arg") && isJust (findAttr (unqual "no") el) && (fromJust $ findAttr (unqual "no") el) == n

getArgAsElement :: String -> Element -> Element
getArgAsElement n el = head $ filterChildren p el where
         p el = elName el == (unqual "arg") && isJust (findAttr (unqual "no") el) && (fromJust $ findAttr (unqual "no") el) == n

createPhiMapping :: [(Context,(Id,FVar))] -> Map.Map Context (Set.Set Context) ->  Map.Map Context [(Id,FVar)]
createPhiMapping x cxtMap = 
      let raw = foldr (\(cxt,pair) m -> Map.insertWith (++) cxt [pair] m) Map.empty x
          aux k v = let ancestors = case Map.member k cxtMap of
                                     False -> []
                                     True -> concat $ Set.toList $ Set.map subaux $ (Map.!) cxtMap k
                        subaux c = case Map.lookup c raw of
                         Just a -> a
                         Nothing -> [] -- error $ "Error in createPhiMapping, when building ancestors, for parent context " ++ c ++ " in raw phi " ++ show raw ++ " with original constraints " ++ show x
                    in v ++ ancestors
      in Map.mapWithKey aux raw

collectPhiMappings :: Element -> [(Context,(Id,FVar))]
collectPhiMappings dom = do
    cStructureElem <- findChildren (unqual "cstructure") dom
    constraint <- findChildren (unqual "constraint") cStructureElem
    guard (hasLabel constraint "phi")
    cxts constraint >>= \cxt -> return (cxt,(read (id constraint), fvar constraint)) where
        cxts el = case findAttr (unqual "context") el of
                Nothing -> [""]
                Just a -> parseContext a
        id el = getArg "1" el
        fvar el = getArg "2" el

collectSubtrees :: Element -> [(Context,BinTree (Id,Label))]
collectSubtrees dom = do
    cStructureElem <- findChildren (unqual "cstructure") dom
    constraint <- findChildren (unqual "constraint") cStructureElem
    guard (isSubTree constraint || isTerminal constraint)
    toContextualizedTree constraint where
      isSubTree el = hasLabel el "subtree"
      isTerminal el = hasLabel el "terminal"
      toContextualizedTree el = cxts >>= \cxt -> return (cxt,t) where
          cxts = case findAttr (unqual "context") el of
                   Nothing -> [""]
                   Just a -> parseContext a
          t = case isTerminal el of
                True -> Terminal (read arg1, arg2) where
                          arg1 = getArg "1" el
                          arg2 = getArg "2" el
                False -> let arg1 = getArg "1" el
                             arg2 = getArg "2" el
                             arg3 = getArg "3" el
                             arg4 = getArg "4" el
                         in case arg3 == "-" of
                            True -> Unary (read arg1,arg2) (Terminal (read arg4, unknown_label))
                            False -> Binary (Terminal (read arg3, unknown_label)) (read arg1, arg2) (Terminal (read arg4, unknown_label))
      

getFStructures :: Element -> [Context] -> Map.Map Context (Set.Set Context) -> EquivalenceMap -> [(Context,FStructure)]
getFStructures dom concreteContexts contextMap equivalenceMap = do
     fconstraints <- return $ collectFConstraints dom
     fconstraints <- return $ expandEquivalenceMap fconstraints equivalenceMap
     guard (not $ null fconstraints)
     currentcontext <- concreteContexts
     return (currentcontext, reconstructFStructure currentcontext contextMap fconstraints)

no_feature = "NO_FEATURE"

collectFConstraints :: Element -> [(Context,(FVar,Feature,Relation,Value))]
collectFConstraints dom = do
     fStructureElem <- findChildren (unqual "fstructure") dom
     constraint <- findChildren (unqual "constraint") fStructureElem
     generateConstraint constraint where
       generateConstraint constr = cxts >>= \cxt -> return (cxt,(fvar,feature,rel,val)) where
          cxts = case findAttr (unqual "context") constr of
                    Nothing -> [""]
                    Just a -> parseContext a
          arg1 = getArgAsElement "1" constr
          arg2 = getArgAsElement "2" constr                                                     
          fvar = case rel of
                   Equality -> getArg "1" arg1
                   InSet -> trim $ strContent arg2
          feature = case rel of
                      Equality -> getArg "2" arg1
                      InSet -> no_feature
          rel = case trim $ strContent $ fromJust $ findChild (unqual "label") constr of
                     "eq" -> Equality
                     "in_set" -> InSet
                     _ -> undefined
          val = case rel of
                   Equality -> valFun arg2
                   InSet -> valFun arg1
          valFun arg = case findChild (unqual "label") arg of
                      Nothing -> let arg2str = trim $ strContent $ arg
                                 in case isPrefixOf "var:" arg2str of
                                   True -> FVar arg2str
                                   False -> Atom arg2str
                      Just _ -> SemForm $ getArg "1" arg
               
reconstructFStructure :: Context -> Map.Map Context (Set.Set Context) -> [(Context,(FVar,Feature,Relation,Value))] -> FStructure
reconstructFStructure cxt contextMap fconstraints = foldr aux Map.empty constraints where
          constraints = (filter (\(c,_) -> c == cxt) fconstraints) ++ ancestorsConstraints
          ancestorsConstraints = concat $ map (\cxt' -> filter (\(c,_) -> c == cxt') fconstraints) (Set.toList $ Map.findWithDefault Set.empty cxt contextMap)
          aux (_,(fvar,feat,Equality,value)) m = Map.insert fvar newVal m where
              newVal = case Map.lookup fvar m of
                            Nothing -> (Set.empty,Map.singleton feat value)
                            Just (s,fmap) -> (s,Map.insert feat value fmap)
          aux (_,(fvar,_,InSet,value)) m = Map.insert fvar newVal m where
              newVal = case Map.lookup fvar m of
                            Nothing -> (Set.singleton (fromValue value), Map.empty)
                            Just (s,fmap) -> (Set.insert (fromValue value) s, fmap)

fromValue (FVar fvar) = fvar
fromValue _ = undefined                

-- Debug and pretty printing

printXMLResults :: FilePath -> IO ()
printXMLResults fp = parseXMLOutput fp >>= mapM_ (\(c,f) -> putStrLn $ (drawCStructure c) ++ "\n" ++ (drawFStructure f))
   