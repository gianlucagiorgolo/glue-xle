module DataStructures where

import Data.Tree
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified DataTypes as DT


data BinTree a = Binary (BinTree a) a (BinTree a)
               | Unary a (BinTree a)
               | Terminal a deriving (Eq, Show)

instance Functor BinTree where
    fmap f (Binary l a r) = Binary (fmap f l) (f a) (fmap f r)
    fmap f (Unary a c) = Unary (f a) (fmap f c)
    fmap f (Terminal a) = Terminal $ f a

getRootValue :: BinTree a -> a
getRootValue (Binary _ a _) = a
getRootValue (Unary a _) = a
getRootValue (Terminal a) = a             

terminals :: BinTree a -> [a]
terminals (Terminal a) = [a]
terminals (Binary l _ r) = (terminals l) ++ (terminals r)
terminals (Unary _ c) = terminals c

type Context = String
type Id = Integer
type Label = String
type FVar = String

type ChoiceTree = Tree Context
type EquivalenceMap = Map.Map Context [Context]

data CStructure = CStructure { tree :: BinTree (Id,Label) 
                             , phiMapping :: Map.Map Id FVar } deriving (Eq,Show)


type FStructure = Map.Map FVar (Set.Set FVar, Map.Map Feature Value) -- the first member of the pair represents the in_set constraints, while the second the feature equalities
type Feature = String
data Value = FVar FVar
           | Atom String
           | SemForm String deriving (Eq,Show)
data Relation = Equality | InSet deriving (Eq,Show)


data SigmaStructure = SigmaStructure { identifier :: Integer
                                     , contents   :: Map.Map Feature SigmaStructure } deriving (Eq,Show)

data SigmaZipper = Top { currentStructure :: SigmaStructure }
                 | Into { featuresPath :: [Feature]
                        , ancestorsIdentifiers :: [Integer]
                        , ancestorDeltaContents :: [Map.Map Feature SigmaStructure]
                        , currentStructure :: SigmaStructure } deriving (Eq,Show)

into :: SigmaZipper -> Feature -> SigmaZipper
into sz@(Top s_struct) feat | Map.member feat (contents s_struct) = Into [feat] [identifier s_struct] [Map.delete feat (contents s_struct)] ((contents s_struct) Map.! feat)
                            | otherwise = sz
into sz@(Into path anc_ids anc_conts s_struct) feat | Map.member feat (contents s_struct) = Into (feat : path) (identifier s_struct : anc_ids) (Map.delete feat (contents s_struct) : anc_conts) ((contents s_struct) Map.! feat)
                                                    | otherwise = sz

top :: SigmaZipper -> SigmaStructure
top (Top s) = s
top (Into [f] [id] [conts] s) = SigmaStructure id (Map.insert f s conts)
top (Into (f : fs) (id : ids) (cont : conts) s) = top $ Into fs ids conts (SigmaStructure id (Map.insert f s cont))

type Type = String

data SigmaConstraint = Variable String Type
                     | SigmaProjection FConstraint Type
                     | SigmaInsideOut [Feature] SigmaConstraint Type -- I doubt it's ever used...
                     | SigmaOutsideIn SigmaConstraint [Feature] Type deriving (Eq, Show, Ord)

data FConstraint = Up
                 | Down
                 | FOutsideIn FConstraint [Feature]
                 | FInsideOut [Feature] FConstraint
                 | FOutsideInSet FConstraint [Feature]
                 | FInsideOutSet [Feature] FConstraint deriving (Eq, Show, Ord)

type Modality = String

data LinearTermTemplate = Atomic SigmaConstraint
                        | LinearImplication LinearTermTemplate LinearTermTemplate
                        | LinearTensor LinearTermTemplate LinearTermTemplate
                        | Diamond Modality LinearTermTemplate deriving (Eq, Show, Ord)

data Template = Template { name :: Name
                         , argumentList :: [Argument]
                         , rawBody :: [RawTemplateBody] } deriving (Eq, Show)

data RawTemplateBody = StringToken String
                     | SpacingToken String
                     | SeparatorToken String
                     | ArgumentToken String
                     | TemplateCallToken TemplateCall deriving (Eq, Show)

data TemplateCall = TemplateCall { callName :: Name
                                 , values :: [String] } deriving (Eq, Show)

type TemplateEnvironment = Map.Map Name Template

expandTemplateCall :: TemplateCall -> TemplateEnvironment -> String
expandTemplateCall tc te = foldr aux "" (rawBody t) where
               t = case Map.lookup (callName tc) te of
                        Nothing -> error $ "Trying to call semantic template " ++ (callName tc) ++ " which is not defined!"
                        Just x -> x
               bindings = Map.fromList $ zip (argumentList t) (values tc) -- should do some error checking, such as the length of the list call...
               aux (StringToken s) acc = s ++ acc
               aux (SpacingToken s) acc = s ++ acc
               aux (SeparatorToken s) acc = s ++ acc
               aux (ArgumentToken s) acc = (bindings Map.! s) ++ acc
               aux (TemplateCallToken call) acc = (expandTemplateCall call te) ++ acc -- if there are recursive calls this thing enters a loop...

type Name = String

type Argument = String

type SigmaProjection = Map.Map FVar SigmaStructure

type Lexicon = Map.Map Token [(DT.LambdaTerm,LinearTermTemplate)]

type Token = String -- for now, we may want to deal with morphology...

type ErrorMessage = String

-- Debug and pretty printing

toTree :: BinTree a -> Tree a
toTree (Binary l a r) = Node a [toTree l,toTree r]
toTree (Unary a c) = Node a [toTree c]
toTree (Terminal a) = Node a []

drawBinTree :: Show a => BinTree a -> String
drawBinTree = drawTree . toTree . fmap show

drawCStructure :: CStructure -> String
drawCStructure (CStructure t phi) = tdraw ++ "\n" ++ phidraw where
           tdraw = drawBinTree t
           phidraw = Map.foldrWithKey aux "" phi
           aux id fvar acc = show id ++ " --> " ++ fvar ++ "\n" ++ acc

drawFStructure :: FStructure -> String
drawFStructure = Map.foldrWithKey aux "" where
      aux fvar (set,featureMap) acc = fvar ++ " --> " ++ show (Set.toList set) ++ "\n" ++ Map.foldrWithKey (aux' $ length fvar) "" featureMap ++ "\n" ++ acc
      aux' l feat val acc = take (l + 5) (repeat ' ') ++ feat ++ " --> " ++ show val ++ "\n" ++ acc

