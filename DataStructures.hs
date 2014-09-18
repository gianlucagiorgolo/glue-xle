module DataStructures where

import Data.Tree
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified DataTypes as DT


data BinTree a = Binary (BinTree a) a (BinTree a)
               | Unary a (BinTree a)
               | Terminal a deriving (Eq, Show)

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
                 | FInsideOut [Feature] FConstraint deriving (Eq, Show, Ord)

type Modality = String

data LinearTermTemplate = Atomic SigmaConstraint
                        | LinearImplication LinearTermTemplate LinearTermTemplate
                        | LinearTensor LinearTermTemplate LinearTermTemplate
                        | Diamond Modality LinearTermTemplate deriving (Eq, Show, Ord)

type SigmaProjection = Map.Map FVar SigmaStructure

type Lexicon = Map.Map Token [(DT.LambdaTerm,LinearTermTemplate)]

type Token = String -- for now, we may want to deal with morphology...

type ErrorMessage = String