module Main where

import Test.HUnit
import System.Exit
-- import Paths_haskell_xle_wrapper

-- XML imports
import XML
import DataStructures
import Text.XML.Light
import Data.Maybe
import Data.Tree
import qualified Data.Set as Set
import Text.Parsec
import Parsers hiding (parseLinearTermTemplate)
import qualified Data.Map as Map

-- Sigma
import Sigma
import qualified DataTypes as DT
import Txt

tests file = TestList [
          xmlTests file ,
          sigmaTests
         ]


-- XML stuff

xmlTests file = TestList [ test_collectContexts
                         , test_contextGroups
                         , test_equivalenceParsing
                         , test_collectEquivalences
                         , test_collectTerminals
                         , test_createContextMap
                         , test_collectSubtrees
                         , test_collectPhiMappings
                         , test_getCStructures file
                         , test_parseContext
                         , test_getFStructures file ]

__testxml0 = fromJust $ parseXMLDoc "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?><analysis type=\"structure\"><packing></packing></analysis>"
__testxml1 = fromJust $ parseXMLDoc "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?><analysis type=\"structure\"><packing><alternatives_for context=\"1\">[A1, A2]</alternatives_for></packing></analysis>"
__testxml2 = fromJust $ parseXMLDoc "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?><analysis type=\"structure\"><packing><alternatives_for context=\"1\">[A1, A2]</alternatives_for><alternatives_for context=\"A1\">[B1,B2]</alternatives_for></packing></analysis>"

test_collectContexts = "collectContexts" ~: TestList 
   [ collectContexts __testxml0 ~?= no_context
   , collectContexts __testxml1 ~?= Node "1" [Node "A1" [], Node "A2" []]
   , collectContexts __testxml2 ~?= Node "1" [Node "A1" [Node "B1" [], Node "B2" []], Node "A2" []] 
   ]



test_contextGroups = "contextGroups" ~: TestList
   [ contextGroups (Node "1" []) ~?= (Set.fromList [Set.fromList ["1"]])
   , contextGroups (Node "1" [Node "A1" [], Node "A2" []]) ~?= (Set.fromList [Set.fromList ["1","A2"], Set.fromList ["1","A1"]])
   ]

test_equivalenceParsing = "equivalence" ~: TestList
   [ fromRight (parse equivalence "" "or(B1,or(A1,A2))") ~?= ["B1","A1","A2"]
   , fromRight (parse equivalence "" "or(B1,A4,or(A1,A2))") ~?= ["B1","A4","A1","A2"]
   ]

test_parseContext = "parseContext" ~: TestList
   [
     parseContext "41" ~?= ["41"]
   , parseContext "or(43,234)" ~?= ["43","234"]
   , parseContext "or(1,2,3,4)" ~?= ["1","2","3","4"]
   ]

__testxml3 = fromJust $ parseXMLDoc "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?><analysis type=\"structure\"><packing><definition_of context=\"CV_001\">or(A1, A2)</definition_of></packing></analysis>"
test_collectEquivalences = "collectEquivalences" ~: TestList
   [
    collectEquivalences __testxml3 ~?= (Map.fromList [("CV_001",["A1","A2"])])
   ]

test_collectTerminals = "collectTerminals" ~: TestList
   [ collectTerminals (Node "a" [Node "b" [], Node "c" [Node "d" [], Node "e" []]]) ~?= ["b","d","e"] ]

test_createContextMap = "createContextMap" ~: TestList
   [createContextMap ["A1","A2"] (Set.fromList [Set.fromList ["1","A2"], Set.fromList ["1","A1"]]) ~?= (Map.fromList [("A1",Set.fromList ["1","A1"]),("A2",Set.fromList ["1","A2"])]) ]

__testxml4 = fromJust $ parseXMLDoc "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?><analysis type=\"structure\"><packing></packing><cstructure><constraint context=\"1\"><label>subtree</label><arg no=\"1\">43</arg><arg no=\"2\">S</arg><arg no=\"3\">21</arg><arg no=\"4\">41</arg></constraint><constraint context=\"1\"><label>phi</label><arg no=\"1\">43</arg><arg no=\"2\">var:0</arg></constraint><constraint context=\"1\"><label>terminal</label><arg no=\"1\">11</arg><arg no=\"2\">the</arg><arg no=\"3\"><label>LIST</label><arg no=\"1\">11</arg></arg></constraint><constraint context=\"1\"><label>phi</label><arg no=\"1\">8</arg><arg no=\"2\">var:4</arg></constraint><constraint context=\"1\"><label>subtree</label><arg no=\"1\">10</arg><arg no=\"2\">P</arg><arg no=\"3\">-</arg><arg no=\"4\">9</arg></constraint><constraint context=\"or(C2, B1)\"><label>subtree</label><arg no=\"1\">50</arg><arg no=\"2\">PP</arg><arg no=\"3\">35</arg><arg no=\"4\">48</arg></constraint></analysis>"

__treesFromTestxml4 = [("1",Binary (Terminal (21, unknown_label)) (43, "S") (Terminal (41, unknown_label))),("1",Terminal (11,"the")),("1",Unary (10,"P") (Terminal (9,unknown_label))),("C2", Binary (Terminal (35,unknown_label)) (50,"PP") (Terminal (48,unknown_label))),("B1", Binary (Terminal (35,unknown_label)) (50,"PP") (Terminal (48,unknown_label)))]

test_collectSubtrees = "collectSubtrees" ~: TestList
   [
     collectSubtrees __testxml4 ~?= __treesFromTestxml4
   ]

test_collectPhiMappings = "collectPhiMappings" ~: TestList
   [
     collectPhiMappings __testxml4 ~?= [("1",(43,"var:0")),("1",(8,"var:4"))]
   ]

test_getCStructures file = "getCStructures" ~: getCStructures dom concCxts cxtMap equivMap ~?= test_xml_file_cstructures where
   dom = fromJust $ parseXMLDoc file
   choiceTree = collectContexts dom
   cxtGroups = contextGroups choiceTree
   equivMap = collectEquivalences dom
   concCxts = collectTerminals choiceTree
   cxtMap = createContextMap concCxts cxtGroups
   test_xml_file_cstructures = [("A1",CStructure t1 phi1), ("A2",CStructure t2 phi2)]
   b id lab l r = Binary l (id,lab) r
   u id lab c = Unary (id,lab) c
   t id lab = Terminal (id,lab)
   t1 = b 43 "S" (u 21 "S" $ u 17 "NP" $ u 2 "N" $ t 1 "Mary") (b 41 "VP" (b 45 "VP" (u 25 "VP" $ u 4 "V" $ t 3 "saw") (b 29 "NP" (u 28 "NP" $ u 6 "D" $ t 5 "a") (u 8 "N" $ t 7 "girl"))) (b 38 "PP" (u 32 "PP" $ u 10 "P" $ t 9 "with") (b 35 "NP" (u 34 "NP" $ u 12 "D" $ t 11 "the") (u 14 "N" $ t 13 "telescope"))))
   phi1 = Map.fromList $ common_phi ++ [p 45 0,p 41 0, p 29 4]
   t2 = b 43 "S" (u 21 "S" $ u 17 "NP" $ u 2 "N" $ t 1 "Mary") (b 41 "VP" (u 25 "VP" $ u 4 "V" $ t 3 "saw") (b 39 "NP" (b 30 "NP" (u 28 "NP" $ u 6 "D" $ t 5 "a") (u 8 "N" $ t 7 "girl")) (b 38 "PP" (u 32 "PP" $ u 10 "P" $ t 9 "with") (b 35 "NP" (u 34 "NP" $ u 12 "D" $ t 11 "the") (u 14 "N" $ t 13 "telescope")))))
   phi2 = Map.fromList $ common_phi ++ [p 41 0,p 39 4, p 30 4]  
   common_phi = [p 43 0, p 38 2, p 35 3, p 34 3, p 32 2, p 28 4, p 25 0, p 21 0, p 17 6, p 14 3, p 13 3, p 12 3, p 11 3, p 10 2, p 9 2, p 8 4, p 7 4, p 6 4, p 5 4, p 4 0, p 3 0, p 2 6 , p 1 6]
   p id v = (id, "var:" ++ show v)

test_getFStructures file = "getFStructures" ~: getFStructures dom concCxts cxtMap equivMap ~?= test_xml_file_fstructures where
   dom = fromJust $ parseXMLDoc file
   choiceTree = collectContexts dom
   cxtGroups = contextGroups choiceTree
   equivMap = collectEquivalences dom
   concCxts = collectTerminals choiceTree
   cxtMap = createContextMap concCxts cxtGroups
   test_xml_file_fstructures = [("A1",fstruct1),("A2",fstruct2)]
   fstruct1 = Map.fromList [("var:0",(Set.empty,Map.fromList $ [("PRED",SemForm "SEE"),("SUBJ",FVar "var:6"),("OBJ",FVar "var:4"),("TENSE",Atom "PAST")] ++ [("ADJUNCT",FVar "var:1")])),("var:6",(Set.empty, Map.fromList $ [("PRED",SemForm "MARY"),("CASE",Atom "NOM"),("NUM",Atom "SG")])),("var:4",(Set.empty,Map.fromList $ [("PRED", SemForm "GIRL"),("CASE",Atom "ACC"),("INDEF",Atom "+"),("NUM",Atom "SG")])),("var:2",(Set.singleton "var:1",Map.fromList $ [("PRED",SemForm "WITH"), ("OBJ",FVar "var:3")])),("var:3",(Set.empty,Map.fromList $ [("CASE",Atom "ACC"),("DEF",Atom "+"),("NUM",Atom "SG"),("PCASE",Atom "WITH"),("PRED",SemForm "TELESCOPE")]))]
   fstruct2 = Map.fromList [("var:0",(Set.empty,Map.fromList $ [("PRED",SemForm "SEE"),("SUBJ",FVar "var:6"),("OBJ",FVar "var:4"),("TENSE",Atom "PAST")])),("var:6",(Set.empty,Map.fromList $ [("PRED",SemForm "MARY"),("CASE",Atom "NOM"),("NUM",Atom "SG")])),("var:4",(Set.empty,Map.fromList $ [("PRED", SemForm "GIRL"),("CASE",Atom "ACC"),("INDEF",Atom "+"),("NUM",Atom "SG")] ++ [("ADJUNCT",FVar "var:5")])),("var:2",(Set.singleton "var:5",Map.fromList $ [("PRED",SemForm "WITH"), ("OBJ",FVar "var:3")])),("var:3",(Set.empty,Map.fromList $ [("CASE",Atom "ACC"),("DEF",Atom "+"),("NUM",Atom "SG"),("PCASE",Atom "WITH"),("PRED",SemForm "TELESCOPE")]))]


-- sigma stuff

sigmaTests = TestList [ test_parseSigmaConstraint
                      , test_parseLinearTermTemplate ]


parseSigmaConstraint e = case parse sigmaConstraint "" e of
                           Right x -> x
                           _ -> undefined

test_parseSigmaConstraint = "parseSigmaConstraint" ~: TestList [
    parseSigmaConstraint "^_s:e" ~?= SigmaProjection Up "e"                     
  , parseSigmaConstraint "(^ SUBJ)_s:e" ~?= SigmaProjection (FOutsideIn Up ["SUBJ"]) "e"
  , parseSigmaConstraint "(^_s VAR):e" ~?= SigmaOutsideIn (SigmaProjection Up "") ["VAR"] "e"
  , parseSigmaConstraint "((SPEC ^)_s RESTR):t" ~?= SigmaOutsideIn (SigmaProjection (FInsideOut ["SPEC"] Up) "") ["RESTR"] "t"
 ]

parseLinearTermTemplate e = case parse linearTermTemplate "" e of
                           Right x -> x
                           Left _ -> undefined

test_parseLinearTermTemplate = "parseLinearTermTemplate" ~: TestList [
    parseLinearTermTemplate "^_s:e" ~?= Atomic (SigmaProjection Up "e")
  , parseLinearTermTemplate "(^ SUBJ)_s:e --o ^_s:t" ~?= LinearImplication (Atomic $ SigmaProjection (FOutsideIn Up ["SUBJ"]) "e") (Atomic $ SigmaProjection Up "t")
  , parseLinearTermTemplate "(^_s VAR):e --o (^_s RESTR):t" ~?= LinearImplication (Atomic $ SigmaOutsideIn (SigmaProjection Up "") ["VAR"] "e") (Atomic $ SigmaOutsideIn (SigmaProjection Up "") ["RESTR"] "t")
  , parseLinearTermTemplate "[((SPEC ^)_s VAR):e --o ((SPEC ^)_s RESTR):t] --o [[(SPEC ^)_s:e --o X:t] --o X:t]" ~?= LinearImplication (LinearImplication (Atomic $ SigmaOutsideIn (SigmaProjection (FInsideOut ["SPEC"] Up) "") ["VAR"] "e") (Atomic $ SigmaOutsideIn (SigmaProjection (FInsideOut ["SPEC"] Up) "") ["RESTR"] "t")) (LinearImplication (LinearImplication (Atomic $ SigmaProjection (FInsideOut ["SPEC"] Up) "e") (Atomic $ Variable "X" "t")) (Atomic $ Variable "X" "t"))
 ]

testWrapper file = runTestTT (tests file)

main = do
  test_xml_file <- return $ "test_data/out.xml" -- getDataFileName "out.xml"
  test_xml_file <- readFile test_xml_file
  counts <- testWrapper test_xml_file
  if errors counts == 0 && failures counts == 0 then exitSuccess else exitFailure

--

foo :: (CStructure,FStructure)
foo = (CStructure {tree = Binary (Unary (11,"S") (Unary (7,"NP") (Unary (2,"N") (Terminal (1,"Mary"))))) (18,"S") (Unary (14,"VP") (Unary (4,"V") (Terminal (3,"sleeps")))), phiMapping = Map.fromList [(1,"var:1"),(2,"var:1"),(3,"var:0"),(4,"var:0"),(7,"var:1"),(11,"var:0"),(14,"var:0"),(18,"var:0")]},Map.fromList [("var:0",(Set.fromList [],Map.fromList [("PRED",SemForm "SLEEP"),("SUBJ",FVar "var:1"),("TENSE",Atom "PRES")])),("var:1",(Set.fromList [],Map.fromList [("CASE",Atom "NOM"),("NUM",Atom "SG"),("PERS",Atom "3"),("PRED",SemForm "MARY")]))])

foo_lex = Map.fromList [("Mary",[parseLinearTermTemplate "^_s:e"]),("sleeps",[parseLinearTermTemplate "(^ SUBJ)_s:e --o ^_s:t"])]

bar :: (CStructure,FStructure)
bar = (CStructure {tree = Binary (Unary (13,"S") (Binary (Unary (9,"DP") (Unary (2,"D") (Terminal (1,"a")))) (12,"DP") (Unary (11,"NP") (Unary (4,"N") (Terminal (3,"cat")))))) (16,"S") (Unary (15,"VP") (Unary (6,"V") (Terminal (5,"sleeps")))), phiMapping = Map.fromList [(1,"var:2"),(2,"var:2"),(3,"var:1"),(4,"var:1"),(5,"var:0"),(6,"var:0"),(9,"var:1"),(11,"var:1"),(12,"var:1"),(13,"var:0"),(15,"var:0"),(16,"var:0")]},Map.fromList [("var:0",(Set.fromList [],Map.fromList [("PRED",SemForm "SLEEP"),("SUBJ",FVar "var:1"),("TENSE",Atom "PRES")])),("var:1",(Set.fromList [],Map.fromList [("NUM",Atom "SG"),("PERS",Atom "3"),("PRED",SemForm "cat"),("SPEC",FVar "var:2")])),("var:2",(Set.fromList [],Map.fromList [("PRED",SemForm "a")]))])

bar_lex = Map.fromList [("a",[parseLinearTermTemplate "[((SPEC ^)_s VAR):e --o ((SPEC ^)_s RESTR):t] --o [[(SPEC ^)_s:e --o X:t] --o X:t]"]),("cat",[parseLinearTermTemplate "(^_s VAR):e --o (^_s RESTR):t"]),("sleeps",[parseLinearTermTemplate "(^ SUBJ)_s:e --o ^_s:t"])]


baz :: (CStructure,FStructure)
baz = (CStructure {tree = Binary (Unary (17,"S") (Binary (Unary (13,"DP") (Unary (2,"D") (Terminal (1,"a")))) (16,"DP") (Unary (15,"NP") (Unary (4,"N") (Terminal (3,"cat")))))) (27,"S") (Binary (Unary (20,"VP") (Unary (6,"V") (Terminal (5,"devours")))) (26,"VP") (Binary (Unary (22,"DP") (Unary (8,"D") (Terminal (7,"a")))) (25,"DP") (Unary (24,"NP") (Unary (10,"N") (Terminal (9,"dog")))))), phiMapping = Map.fromList [(1,"var:4"),(2,"var:4"),(3,"var:3"),(4,"var:3"),(5,"var:0"),(6,"var:0"),(7,"var:2"),(8,"var:2"),(9,"var:1"),(10,"var:1"),(13,"var:3"),(15,"var:3"),(16,"var:3"),(17,"var:0"),(20,"var:0"),(22,"var:1"),(24,"var:1"),(25,"var:1"),(26,"var:0"),(27,"var:0")]},Map.fromList [("var:0",(Set.fromList [],Map.fromList [("OBJ",FVar "var:1"),("PRED",SemForm "DEVOUR"),("SUBJ",FVar "var:3"),("TENSE",Atom "PRES")])),("var:1",(Set.fromList [],Map.fromList [("PRED",SemForm "dog"),("SPEC",FVar "var:2")])),("var:2",(Set.fromList [],Map.fromList [("PRED",SemForm "a")])),("var:3",(Set.fromList [],Map.fromList [("NUM",Atom "SG"),("PERS",Atom "3"),("PRED",SemForm "cat"),("SPEC",FVar "var:4")])),("var:4",(Set.fromList [],Map.fromList [("PRED",SemForm "a")]))])

baz_lex = Map.fromList [("a",[(DT.C "some",parseLinearTermTemplate "[((SPEC ^)_s VAR):e --o ((SPEC ^)_s RESTR):t] --o [[(SPEC ^)_s:e --o X:t] --o X:t]")]),("cat",[(DT.C "cat",parseLinearTermTemplate "(^_s VAR):e --o (^_s RESTR):t")]),("sleeps",[(DT.C "sleep",parseLinearTermTemplate "(^ SUBJ)_s:e --o ^_s:t")]),("dog",[(DT.C "dog",parseLinearTermTemplate "(^_s VAR):e --o (^_s RESTR):t")]),("devours",[(DT.C "devour",parseLinearTermTemplate "(^ SUBJ)_s:e --o (^ OBJ)_s:e --o ^_s:t")])]

-- testCreation cf lex = map (map (\(l,f) -> lambda2text l ++ " : " ++ formula2text f)) $ createResourcePool cf lex