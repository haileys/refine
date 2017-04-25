import Control.Monad.State
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.List as List

type TypeId = Int

data Type
    = Int
    | Str
    | TyTrue
    | Nil
    | List Type
    | TyFun Type Type
    | Union Type Type
    | TyVar TypeId

data TyGen
    = Template Type
    | Instance Type
    | TyGen TypeId TyGen

typeEq :: Type -> Type -> TyState Bool
typeEq a b = do
    a <- prune a
    b <- prune b
    case (a, b) of
        (Int, Int) -> return True
        (Str, Str) -> return True
        (TyTrue, TyTrue) -> return True
        (Nil, Nil) -> return True
        ((List a), (List b)) -> typeEq a b
        ((TyFun a a'), (TyFun b b')) -> do
            aEq <- typeEq a a'
            bEq <- typeEq b b'
            return (aEq && bEq)
        (a@(Union _ _), b@(Union _ _)) -> do
            as <- possibleTypes a
            bs <- possibleTypes b
            eqs <- mapM (elemByM typeEq bs) as
            return $ all id eqs
        ((TyVar a), (TyVar b)) -> return (a == b)

elemByM :: Monad m => (a -> a -> m Bool) -> [a] -> a -> m Bool
elemByM _ [] _ = return False
elemByM eq (x:xs) y = do
    cmp <- eq x y
    if cmp then return True else elemByM eq xs y

unionByM :: Monad m => (a -> a -> m Bool) -> [a] -> [a] -> m [a]
unionByM eq as [] = return as
unionByM eq as (x:xs) = do
    isElem <- elemByM eq as x
    if isElem then
        unionByM eq as xs
    else
        unionByM eq (x:as) xs

possibleTypes :: Type -> TyState [Type]
possibleTypes ty = possibleTypes' ty []
    where possibleTypes' ty tys = do
            ty <- prune ty
            case ty of
                (Union a b) -> possibleTypes' b tys >>= possibleTypes' a
                _ -> return (ty : tys)

data TyEnv = TyEnv TypeId (Map.Map TypeId Type)

type TyState t = State TyEnv t

newtyenv :: TyEnv
newtyenv = TyEnv 0 Map.empty

runTy :: TyState a -> a
runTy state = evalState state newtyenv

showTy :: Type -> TyState String
showTy ty = do
    ty <- prune ty
    case ty of
        Int -> return "Int"
        Str -> return "Str"
        TyTrue -> return "True"
        Nil -> return "Nil"
        (List t) -> do
            tstr <- showTy t
            return ("[" ++ tstr ++ "]")
        (TyFun t t') -> do
            tstr <- showTy t
            t'str <- showTy t'
            return (tstr ++ " -> " ++ t'str)
        (Union a b) -> do
            astr <- showTy a
            bstr <- showTy b
            return (astr ++ "|" ++ bstr)
        (TyVar tyid) -> return ("t" ++ show tyid)

prune :: Type -> TyState Type
prune ty@(TyVar tyid) = do
    tyenv@(TyEnv _ tymap) <- get
    case Map.lookup tyid tymap of
        Just resolved -> prune resolved
        Nothing -> return ty
prune ty = return ty

newtyvar :: TyState Type
newtyvar = do
    (TyEnv tyid tymap) <- get
    put (TyEnv (succ tyid) tymap)
    return (TyVar tyid)

mkunion :: Type -> Type -> TyState Type
mkunion a b = do
    as <- possibleTypes a
    bs <- possibleTypes b
    (ty:tys) <- unionByM typeEq as bs
    return $ foldl Union ty tys

joinMaybeTypes :: Maybe Type -> Maybe Type -> TyState (Maybe Type)
joinMaybeTypes (Just a) (Just b) = Just `fmap` mkunion a b
joinMaybeTypes (Just a) Nothing = return (Just a)
joinMaybeTypes Nothing (Just b) = return (Just b)
joinMaybeTypes Nothing Nothing = return Nothing

filterType :: Type -> (Type -> TyState Bool) -> TyState (Maybe Type, Maybe Type)
filterType ty f = do
    ty <- prune ty
    case ty of
        (Union a b) -> do
            (aTrue, aFalse) <- filterType a f
            (bTrue, bFalse) <- filterType b f
            aJoin <- joinMaybeTypes aTrue bTrue
            bJoin <- joinMaybeTypes aFalse bFalse
            return (aJoin, bJoin)
        _ -> do
            ok <- f ty
            return $ if ok
                then (Just ty, Nothing)
                else (Nothing, Just ty)

unifyError :: Type -> Type -> TyState t
unifyError a b = do
    astr <- showTy a
    bstr <- showTy b
    error $ "type mismatch: " ++ astr ++ " and " ++ bstr

setTyVar :: TypeId -> Type -> TyState ()
setTyVar tyid ty = modify $ \(TyEnv nextid tymap) ->
    TyEnv nextid (Map.insert tyid ty tymap)

unify :: Type -> Type -> TyState ()
unify a b = do
    a <- prune a
    b <- prune b

    case (a, b) of
        ((TyVar a), (TyVar b)) | a == b -> error "recursive type unification"
        ((TyVar a), b) -> setTyVar a b
        (a, (TyVar b)) -> setTyVar b a
        (Int, Int) -> return ()
        (Str, Str) -> return ()
        (TyTrue, TyTrue) -> return ()
        (Nil, Nil) -> return ()
        (List a, List b) -> unify a b
        (TyFun a a', TyFun b b') -> unify a b >> unify a' b'
        (a@(Union _ _), b@(Union _ _)) -> do
            eq <- typeEq a b
            if eq then return () else unifyError a b
        (a, b) -> unifyError a b

constructType :: TyGen -> TyState Type
constructType tygen = constructType' tygen Map.empty
    where constructType' tygen genmap = case tygen of
            TyGen tyid ty -> do
                tyvar <- newtyvar
                constructType' ty $ Map.insert tyid tyvar genmap
            Template (TyVar tyid) ->
                case Map.lookup tyid genmap of
                    Just ty -> return ty
                    Nothing -> error $ "unknown type id in generic type: " ++ show tyid
            Template Int -> return Int
            Template Str -> return Str
            Template TyTrue -> return TyTrue
            Template Nil -> return Nil
            Template (List elementgen) -> do
                element <- constructType' (Template elementgen) genmap
                return (List element)
            Template (TyFun arggen resgen) -> do
                arg <- constructType' (Template arggen) genmap
                res <- constructType' (Template resgen) genmap
                return (TyFun arg res)
            Template (Union agen bgen) -> do
                a <- constructType' (Template agen) genmap
                b <- constructType' (Template bgen) genmap
                return (Union a b)
            Instance ty -> return ty

truthy :: Type -> Bool
truthy Nil = False
truthy (Union a b) = truthy a || truthy b
truthy _ = True

falsy :: Type -> Bool
falsy Nil = True
falsy (Union a b) = falsy a || falsy b
falsy _ = False

type Id = String

type Bindings = Map.Map Id TyGen

data Computation
    = Result Bindings Type
    | CompReturn Bindings Type
    | Divergent Computation Computation

mapEval :: (Bindings -> Type -> TyState Computation) -> Computation -> TyState Computation
mapEval f (Result bind ty) = f bind ty
mapEval f (CompReturn bind ty) = do
    f bind ty
    return (CompReturn bind ty)
mapEval f (Divergent comp1 comp2) = do
    comp1' <- mapEval f comp1
    comp2' <- mapEval f comp2
    return (Divergent comp1' comp2')

joinMaybeComps :: Maybe Computation -> Maybe Computation -> Maybe Computation
joinMaybeComps (Just a) (Just b) = Just (Divergent a b)
joinMaybeComps a@(Just _) Nothing = a
joinMaybeComps Nothing b@(Just _) = b
joinMaybeComps Nothing Nothing = Nothing

filterComp :: (Type -> Bool) -> Computation -> Maybe Computation
filterComp f comp@(Result _ ty)
    | f ty = Just comp
    | otherwise = Nothing
filterComp f comp@(CompReturn _ ty)
    = Nothing
filterComp f (Divergent c1 c2)
    = joinMaybeComps (filterComp f c1) (filterComp f c2)

returns :: Computation -> Maybe Computation
returns (Result _ _) = Nothing
returns comp@(CompReturn _ _) = Just comp
returns (Divergent c1 c2) = joinMaybeComps (returns c1) (returns c2)

compType :: Computation -> TyState (Maybe Type)
compType (Result _ ty) = return (Just ty)
compType (CompReturn _ _) = return (Nothing)
compType (Divergent c1 c2) = do
    t1 <- compType c1
    t2 <- compType c2
    joinMaybeTypes t1 t2

data Expr
    = Apply Expr Expr
    | Let Id Expr
    | If Expr Expr Expr
    | Seq Expr Expr
    | Lit Type
    | Var Id
    | InstanceOf Expr TyGen
    | Return Expr

seqEval :: Bindings -> Expr -> (Bindings -> Type -> TyState Computation) -> TyState Computation
seqEval bindings expr f =
    eval bindings expr >>= mapEval f

lookupVar :: Bindings -> Id -> TyState Type
lookupVar bindings id_ = case Map.lookup id_ bindings of
    Just tygen -> constructType tygen
    Nothing -> error $ "no such binding '" ++ id_ ++ "' in scope"

eval :: Bindings -> Expr -> TyState Computation

eval bindings (Apply fun arg) =
    seqEval bindings fun $ \bindings funty ->
        seqEval bindings arg $ \bindings argty -> do
            funargvar <- newtyvar
            funresvar <- newtyvar
            unify (TyFun funargvar funresvar) funty
            unify funargvar argty
            return (Result bindings funresvar)

eval bindings (Let id_ expr) =
    seqEval bindings expr $ \bindings exprType ->
        let bindings = Map.insert id_ (Instance exprType) bindings
        in return (Result bindings exprType)

eval bindings (If cond then_ else_) = do
    condComp <- eval bindings cond

    thenComp <- case filterComp truthy condComp of
        Just comp -> Just `fmap`
            mapEval (\trueBindings _ -> eval trueBindings then_) comp
        Nothing -> return Nothing

    elseComp <- case filterComp falsy condComp of
        Just comp -> Just `fmap`
            mapEval (\falseBindings _ -> eval falseBindings else_) comp
        Nothing -> return Nothing

    let divergent = joinMaybeComps thenComp
                  $ joinMaybeComps elseComp
                  $ returns condComp

    -- at least one of thenComp, elseComp or retComp *must* be Just:
    return $ fromJust divergent

eval bindings (Seq a b) =
    seqEval bindings a $ \bindings _ ->
        eval bindings b

eval bindings (Lit ty) =
    return $ Result bindings ty

eval bindings (Var id_) = do
    ty <- lookupVar bindings id_
    return (Result bindings ty)

eval bindings (InstanceOf (Var id_) tygen) = do
    varType <- lookupVar bindings id_
    let varTypes = possibleTypes varType
    ty <- constructType tygen
    (ofTy, other) <- filterType ty (typeEq ty)

    return $ fromJust $ joinMaybeComps
        (fmap (\t -> (Result (Map.insert id_ (Instance t) bindings) TyTrue)) ofTy)
        (fmap (\t -> (Result (Map.insert id_ (Instance t) bindings) Nil)) other)

eval bindings (Return expr) = do
    seqEval bindings expr $ \bindings exprType ->
        return (CompReturn bindings exprType)

booleanType :: Type
booleanType = Union Nil TyTrue

globals :: Bindings
globals = Map.fromList [
    ("+",       Instance (TyFun Int (TyFun Int Int))),
    ("-",       Instance (TyFun Int (TyFun Int Int))),
    ("*",       Instance (TyFun Int (TyFun Int Int))),
    ("/",       Instance (TyFun Int (TyFun Int Int))),
    ("<",       Instance (TyFun Int (TyFun Int booleanType))),
    ("<=",      Instance (TyFun Int (TyFun Int booleanType))),
    (">",       Instance (TyFun Int (TyFun Int booleanType))),
    (">=",      Instance (TyFun Int (TyFun Int booleanType))),
    ("==",      Instance (TyFun Int (TyFun Int booleanType))),
    ("++",      Instance (TyFun Str (TyFun Str Str))),
    ("print",   Instance (TyFun Str Nil)),
    ("map",     TyGen 0 (TyGen 1 (Template (
                    TyFun (TyFun (TyVar 0) (TyVar 1)) (TyFun (List (TyVar 0)) (List (TyVar 1)))))))
    ]

main :: IO ()
main =
    let lit ty = Lit ty
        apply fn args = foldl Apply fn args
        ast = apply (Var "map") [lit (List Int)]
    in print $ runTy $ do
        comp <- eval globals ast
        cty <- compType comp
        case cty of
            Just ty -> showTy ty
            Nothing -> return "⊥"
