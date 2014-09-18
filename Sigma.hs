module Sigma where

import DataStructures
import qualified Data.Map as Map
import Data.Maybe
import DataTypes
import Control.Monad.State
import Data.List


data InstantiationState = InstantiationState { sigmaProj :: SigmaProjection,
                                               accumulator :: Integer,
                                               localVarNames :: Map.Map String String } deriving (Eq, Show)

generateNewSigmaVarIdentifier :: Control.Monad.State.State InstantiationState Integer
generateNewSigmaVarIdentifier = do
   is <- get
   n <- return $ accumulator is
   put is{accumulator = n + 1}
   return n

getSigmaProjection :: Control.Monad.State.State InstantiationState SigmaProjection
getSigmaProjection = get >>= \is -> return $ sigmaProj is

updateSigmaProjection :: FVar -> SigmaStructure -> Control.Monad.State.State InstantiationState ()
updateSigmaProjection fvar s_struct = do
   is <- get
   put is{sigmaProj = Map.insert fvar s_struct (sigmaProj is)}

getStructureName :: SigmaStructure -> String
getStructureName ss = "x" ++ show (DataStructures.identifier ss)

newState :: InstantiationState
newState = InstantiationState Map.empty 0 Map.empty

clearLocalVarNames :: Control.Monad.State.State InstantiationState ()
clearLocalVarNames = do
   is <- get
   put is{localVarNames = Map.empty}

getVarInstanceName :: String -> Control.Monad.State.State InstantiationState String
getVarInstanceName s = do
   is <- get
   m <- return $ localVarNames is
   case Map.lookup s m of
        Just name -> return name
        Nothing -> do
            i <- generateNewSigmaVarIdentifier
            name <- return $ s ++ show i
            is <- get
            put is{localVarNames=Map.insert s name m}
            return name

emptySigmaStructure :: Integer -> SigmaStructure
emptySigmaStructure n = SigmaStructure n Map.empty

addFeature :: SigmaStructure -> Feature -> SigmaStructure -> SigmaStructure
addFeature old f v = old{ contents = Map.insert f v (contents old) }

instantiateSigmaConstraint :: SigmaConstraint -> FStructure -> FVar -> Control.Monad.State.State InstantiationState (String,DataStructures.Type,FVar)
instantiateSigmaConstraint (Variable name ty) _ fvar = getVarInstanceName name >>= \name' -> return (name',ty,fvar)
instantiateSigmaConstraint (SigmaProjection fc ty) f_struct fvar = do
    fvar' <- return $ followPath fvar fc f_struct
    sProj <- getSigmaProjection
    case Map.lookup fvar' sProj of
       Just s_struct -> return (getStructureName s_struct,ty,fvar')
       Nothing -> do
          id <- generateNewSigmaVarIdentifier
          s_struct <- return $ emptySigmaStructure id
          updateSigmaProjection fvar' s_struct
          return (getStructureName s_struct,ty,fvar')
instantiateSigmaConstraint (SigmaOutsideIn sc feats ty) f_struct fvar = do
    (_,_,fvar') <- instantiateSigmaConstraint sc f_struct fvar
    sProj <- getSigmaProjection
    starting_s_struct <- return $ sProj Map.! fvar' -- we can use Map.! because the s_struct must exist given the recursive call we make above
    target_s_struct <- followSigmaPath fvar' feats starting_s_struct
    return (getStructureName target_s_struct,ty,dummy_fvar)
instantiateSigmaConstraint (SigmaInsideOut _ _ _) _ _ = error "Not implemented -- probably because it's useless"

followSigmaPath :: FVar -> [Feature] -> SigmaStructure -> Control.Monad.State.State InstantiationState SigmaStructure
followSigmaPath _ [] s = return s
followSigmaPath fvar feats s_struct = aux (Top s_struct) feats where
    aux zipper [] = do
       updateSigmaProjection fvar (top zipper)
       return $ currentStructure zipper
    aux zipper (f : fs) = do
       zipper' <- return $ into zipper f
       case zipper == zipper' of
          True -> do
            n <- generateNewSigmaVarIdentifier
            zipper' <- return $ zipper'{currentStructure = addFeature (currentStructure zipper) f (emptySigmaStructure n)}
            aux zipper' (f : fs)
          False -> aux zipper' fs
            
           
followPath :: FVar -> FConstraint -> FStructure -> FVar
followPath fvar Up _ = fvar
followPath _ Down _ = error "Down path not implemented"
followPath fvar (FOutsideIn fc features) f_struct = aux features fvar' where
           fvar' = followPath fvar fc f_struct
           aux [] fvar = fvar
           aux (f : fs) fvar = case Map.lookup fvar f_struct of
                                    Nothing -> error $ "Mmmmmm there's something weird with the f-structure"
                                    Just m -> case Map.lookup f (snd m) of
                                                   Nothing -> error $ "The feature " ++ f ++ " is not present in the f-structure, maybe there's some problem in the lexicon?"
                                                   Just v -> case v of 
                                                       FVar fvar -> aux fs fvar
                                                       _ -> error $ "Ooops, the feature " ++ f ++ " doesn't seem to have another f-structure as value, this is not good..."
followPath fvar (FInsideOut features fc) f_struct = aux features fvar' where
         tmp1 = Map.map snd f_struct
         tmp2 = Map.map (\m -> Map.foldrWithKey f Map.empty m) tmp1
         reversed_f_struct = reverseMap tmp2
         f feat (FVar fvar) m = Map.insert feat fvar m
         f _ _ m = m
         fvar' = followPath fvar fc f_struct
         aux [] fvar = fvar
         aux (f : fs) fvar = case Map.lookup fvar reversed_f_struct of
                                  Nothing -> error $ "Mmmmmm there's something weird with the f-structure"
                                  Just m -> case Map.lookup f m of
                                                 Nothing -> error $ "The feature " ++ f ++ " is not present in the f-structure, maybe there's some problem in the lexicon?"
                                                 Just fvar -> aux fs fvar

reverseMap :: (Ord c, Ord b) => Map.Map a (Map.Map b c) -> Map.Map c (Map.Map b a)
reverseMap m = foldr (\(a,bcs) m' -> foldr (f a) m' bcs) Map.empty $ Map.toList $ Map.map Map.toList m where
           f a (b,c) m = Map.insertWith Map.union c (Map.singleton b a) m
         
dummy_fvar = "var:-666"    


isVar (Variable _ _) = True
isVar _ = False                

instantiate :: LinearTermTemplate -> FStructure -> FVar -> Control.Monad.State.State InstantiationState Formula
instantiate (Atomic sc) f_struct fvar = do
    (name,ty,_) <- instantiateSigmaConstraint sc f_struct fvar
    case isVar sc of
         False -> return $ DataTypes.Atom name (TAtomic ty)
         True -> return $ Var name (TAtomic ty)
instantiate (LinearImplication l r) f_struct fvar = do
    l_f <- instantiate l f_struct fvar
    r_f <- instantiate r f_struct fvar
    return $ I l_f r_f (TFunctional (getType l_f) (getType r_f))
instantiate (LinearTensor l r) f_struct fvar = do
    l_f <- instantiate l f_struct fvar
    r_f <- instantiate r f_struct fvar
    return $ P l_f r_f (TPair (getType l_f) (getType r_f))
instantiate (Diamond _ c) f_struct fvar = do
    c_f <- instantiate c f_struct fvar
    return $ M c_f (TMonadic $ getType c_f) -- for now we disregard the modality because I'm testing the unimodal version

prod :: [[a]] -> [[a]]
prod [] = []
prod [a] = [a]
prod (h : t) = do
    a <- h
    as <- prod t
    return $ a : as

createResourcePool :: (CStructure,FStructure) -> Lexicon -> [([(DataTypes.LambdaTerm,Formula)],Formula)]
createResourcePool (c_struct, f_struct) lex = do
      words <- return $ terminals $ tree c_struct
      templates <- return $ map (\(id,x) -> (id,Map.lookup x lex)) words
      guard (all (isJust . snd) templates)
      templates <- return $ map (\(id, Just ts) -> map (\t -> (id,fst t,snd t)) ts) templates
      pool <- prod templates
      lhsResources <- return $ evalState (mapM (\(i,l,t) -> instantiate t f_struct ((phiMapping c_struct) Map.! i) >>= \res -> clearLocalVarNames >> return (i,l,res)) pool) newState
      rootFvar <- return $ getRootFVar c_struct
      mainHeadId <- return $ getCopointingTreeId words (phiMapping c_struct) rootFvar
      rhsFormula <- return $ positiveResource $ (\(_,_,t) -> t) $ fromJust $ find (\(i,_,_) -> i == mainHeadId) lhsResources
      return (map (\(_,l,t) -> (l,t)) lhsResources,rhsFormula)

getRootFVar :: CStructure -> FVar
getRootFVar c_struct = (phiMapping c_struct) Map.! (fst $ getRootValue $ tree c_struct) 

getCopointingTreeId :: [(Id,DataStructures.Label)] -> (Map.Map Id FVar) -> FVar -> Id
getCopointingTreeId [] _ _ = error $ "should not be reachable"
getCopointingTreeId ((id,_) : rest) m fvar = case m Map.! id == fvar of
                                                  True -> id
                                                  False -> getCopointingTreeId rest m fvar

positiveResource :: Formula -> Formula
positiveResource a@(DataTypes.Atom _ _) = a
positiveResource v@(Var _ _) = v
positiveResource m@(M _ _) = m
positiveResource p@(P _ _ _) = p
positiveResource (I _ r _) = positiveResource r
