{-# LANGUAGE OverloadedStrings, BangPatterns, LambdaCase, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Compiler where

import Control.Monad.State.Strict
import Control.Monad.Writer
import qualified Table as T; import Table (Table(..))
import qualified Data.Map as M
import Data.Map (Map, (!))
import Data.List 
import Data.Foldable
import Data.String
import Control.Exception (assert)
import Data.Maybe

import Debug.Trace

-- constant value
type W = Int

-- expression functor
data EF a =
  EVV Int |           -- (virtual value)
  EK W |              -- 3
  EBV String |        -- x
  EPV String Int |    -- x
  ESK String |        -- x
  EBiop OpTag2 a a |
  EUnop OpTag1 a |
--  EAdd a a |          -- e + e
--  ESub a a |          -- e - e
--  ENeg a |            -- -e
--  ELoad a a |         -- e[e]
  ELet String a a |   -- let x = e in e
  ECall a [a] |       -- e(e,e,e)
  EQue a a a          -- e ? e : e
    deriving (Show,Functor,Foldable,Traversable)

data OpTag2 = Op2Add | Op2Sub | Op2Load deriving Show
data OpTag1 = Op1Neg deriving Show

-- bare expression tree
newtype E = E (EF E) deriving Show

-- labeled expression tree
data LE = LE LabelE (EF LE) deriving Show

lab (LE l _) = l

-- labels for expressions and for values
newtype LabelE = LLE Int deriving (Show,Eq,Ord)
newtype LabelV = LLV Int deriving (Show,Eq,Ord)

-- storage location names
data Storage =
  Register Int |
  ArgMem Int |
  SavesMem Int |
  TempMem Int |
  ExpMem Int
  deriving (Eq,Ord,Show)

-- symbolic address for symcode instructions
data SymAddr =
  SAK W | SAR Int | SAName String |
  SAVFBase | SAVFSaves | SAVFTemps | SAVFExpansion
    deriving Show

-- sak is a known numeric constant
-- sar is a specific register
-- saname is a symbolic constant, to be filled in later
-- savfbase is the symbolic stack address of the base of the current frame
--   the base is 1 address above the return address on the stack
--   zero or more extra arguments are stored beginning at the base
-- savftemps is 1 address above the extra arguments, or equal to base
--   when there are no extra arguments
-- savfexpansion is 1 address above the temps. is used specifically during
--   the tailcall-with-extra-args situation to juggle extra args. this is
--   also the location to place the return address for a normal call, and
--   the next virtual frame would begin after this. the expansion area does
--   not survive a call.

data SymCodeF a =
  SCopy a a |
  SAdd a a a |
  SSub a a a |
  SNeg a a |
  SCall a |
  STailCall a |
  SLoad a a a |
  SStore a a a |
  SReturn |
  SRestorePlaceholder |
  SSplit a [SymCodeF a] [SymCodeF a]
    deriving (Functor, Show)

type SymCode = SymCodeF SymAddr

data CompilerState = CS
  { csRegisterCount :: Int
  , csFastArgCount :: Int
  , csStorageMap :: Table Storage LabelV
  , csGlobalTree :: LE
  , csLocalTree :: LE
  , csValueMap :: Map LabelE LabelV
  , csSavedSet :: [Int]
  , csMaxSlowArgs :: Int
  , csCodeBuilder :: [SymCode] -> [SymCode] }

type Compiler a = State CompilerState a

symOp2 Op2Add = SAdd
symOp2 Op2Sub = SSub
symOp2 Op2Load = SLoad
symOp1 Op1Neg = SNeg

isRegister :: Storage -> Bool
isRegister (Register _) = True
isRegister _ = False

isMemory :: Storage -> Bool
isMemory (ArgMem _) = True
isMemory (TempMem _) = True
isMemory _ = False

queryStorage :: Storage -> Compiler (Maybe LabelV)
queryStorage addr = do
  sto <- gets csStorageMap
  case T.lookupL addr sto of
    [] -> pure Nothing
    [v] -> pure (Just v)
    _ -> error "multiple values in storage location"

forgetStorage :: Storage -> Compiler ()
forgetStorage addr = do
  sto <- gets csStorageMap
  modify (\s -> s { csStorageMap = T.deleteL addr sto })

rememberStorage :: Storage -> LabelV -> Compiler ()
rememberStorage addr v = do
  sto <- gets csStorageMap
  modify (\s -> s { csStorageMap = T.insert addr v (T.deleteL addr sto) })

getValueOf :: LabelE -> Compiler LabelV
getValueOf l = do
  vals <- gets csValueMap
  case M.lookup l vals of
    Nothing -> error ("getValueOf: " ++ show l)
    Just v  -> pure v

getLocationsOf :: LabelV -> Compiler [Storage]
getLocationsOf v = do
  sto <- gets csStorageMap
  pure $ T.lookupR v sto

useSavedReg :: Int -> Compiler ()
useSavedReg i = do
  (_,saveds) <- clobberableOrNotRegs
  when (i `elem` saveds) $ do
    set <- gets csSavedSet
    modify (\s -> s { csSavedSet = [i] `union` set  })

bumpSlowArgs :: Int -> Compiler ()
bumpSlowArgs n = do
  m <- gets csMaxSlowArgs
  modify (\s -> s { csMaxSlowArgs = max n m })

emit :: SymCode -> Compiler ()
emit code = do
  f <- gets csCodeBuilder
  modify (\s -> s { csCodeBuilder = (++ [code]) . f })

registers :: Compiler [Int]
registers = do
  n <- gets csRegisterCount
  return [0..n-1]

bestLocation :: [Storage] -> Maybe Storage
bestLocation locs = case sort locs of
  [] -> Nothing
  (loc:_) -> Just loc

blankCS :: CompilerState
blankCS = CS
  { csRegisterCount = undefined
  , csFastArgCount = undefined
  , csGlobalTree = undefined
  , csLocalTree = undefined
  , csValueMap = undefined
  , csStorageMap = undefined
  , csMaxSlowArgs = 0
  , csSavedSet = []
  , csCodeBuilder = id }

-- some expressions are assigned a value label to stand for the identity
-- of an unknown value that we may compute at runtime. constant values are
-- known at compile time, take up no resources, and dont get a value label.
--
-- this code is really bad
mkValueOf :: [String] -> LE -> Map LabelE LabelV
mkValueOf args le = snd $ execState (go [] le) (length args, M.empty) where
  go :: [(String,LabelV)] -> LE -> State (Int,Map LabelE LabelV) ()
  go env (LE l e) = case e of
    EK w -> boring l
    ESK _ -> boring l
    EPV x i -> enter l (LLV i)
    EBV x -> case lookup x env of
      Just v  -> enter l v -- bound variable (not constant)
      Nothing -> pure ()   -- assumed to be symbolic constant
    EUnop _ e1 -> do boring l; go env e1
    EBiop _ e1 e2 -> do boring l; go env e1; go env e2
    ELet y e1 e2 -> do
      go env e1
      m <- gets snd
      let env' = case M.lookup (lab e1) m of
                    Just v1 -> (y,v1) : env
                    Nothing -> env
      go env' e2
      m <- gets snd
      case M.lookup (lab e2) m of
        Just v2 -> enter l v2
        Nothing -> pure ()
    ECall ef es -> do boring l; go env ef; mapM_ (go env) es
    EQue e1 e2 e3 -> do
      go env e1
      go env e2
      go env e3
      v4 <- LLV <$> takeI
      enter l v4
  enter :: LabelE -> LabelV -> State (Int, Map LabelE LabelV) ()
  enter l v = do
    (i,m) <- get
    put (i, M.insert l v m)
  takeI = do
    (i,m) <- get
    put (i+1,m)
    return i
  boring l = do
    v <- fmap LLV takeI
    enter l v

nodupInsert :: Eq a => a -> [a] -> [a]
nodupInsert y [] = [y]
nodupInsert y (x:xs)
  | x == y    = (x:xs)
  | otherwise = x : nodupInsert y xs

labelExpression :: E -> State [Int] LE
labelExpression (E pay) = do
  i <- takeNumber
  pay' <- traverse labelExpression pay
  return (LE (LLE i) pay')

takeNumber :: State [Int] Int
takeNumber = do
  (i:is) <- get
  put is
  return i



-- debugging

vizStorage :: Table Storage LabelV -> String
vizStorage sto = unlines vlines where
  vlines = map f vs
  vs = T.elemsR sto
  f v@(LLV i) = "v" ++ show i ++ ": " ++ intercalate " " (map g (sort $ T.lookupR v sto))
  g (Register i) = "r" ++ show i
  g (ArgMem i) = "base[" ++ show i ++ "]"
  g (TempMem i) = "temp[" ++ show i ++ "]"
  g (ExpMem i) = "exp[" ++ show i ++ "]"

dumpSto :: String -> Compiler ()
dumpSto hint = do
  sto <- gets csStorageMap
  traceM (hint ++ "\n" ++ vizStorage sto)

dumpSto' :: String -> CompilerState -> Compiler ()
dumpSto' hint cs = do
  let sto = csStorageMap cs
  traceM (hint ++ "\n" ++ vizStorage sto)

debugM :: String -> Compiler ()
debugM msg = do
  traceM msg
  return ()

substituteExpr :: LabelE -> LE -> LE -> LE
substituteExpr l sub host = go host where
  go (LE l' e) | l == l' = sub
               | otherwise = (LE l') $ case e of
    EUnop op e1 -> EUnop op (go e1)
    EBiop op e1 e2 -> EBiop op (go e1) (go e2)
    ELet y e1 e2 -> ELet y (go e1) (go e2)
    ECall ef es -> ECall (go ef) (map go es)
    EQue e1 e2 e3 -> EQue (go e1) (go e2) (go e3)
    _ -> e

-- assuming LE is not a "final pattern"
nextComputation :: LE -> LE
nextComputation root = assuming (getFirst (go root)) where
  go le@(LE l e) = case e of
    EUnop _ e1 -> go e1 <> First (Just le)
    EBiop _ e1 e2 -> go e1 <> go e2 <> First (Just le)
    ELet x e1 e2 -> go e1 <> First (Just le)
    ECall ef es -> go ef <> mconcat (map go es) <> First (Just le)
    EQue e1 e2 e3 -> go e1 <> First (Just le)
    _ -> First Nothing
  assuming (Just le) = le
  assuming Nothing = error "nextComputation assumes fish needs frying"

activeValues :: LE -> [LabelV]
activeValues root = nub (go [] root) where
  go out (LE l e) = case e of
    EVV i -> LLV i : out
    EPV _ i -> LLV i : out
    EUnop _ e1 -> go out e1
    EBiop _ e1 e2 -> go (go out e1) e2
    ELet x e1 e2 -> go (go out e1) e2
    ECall ef es -> foldl go (go out ef) es
    EQue e1 e2 e3 -> go (go (go out e1) e2) e3
    _ -> out


-- copy value in register to memory, *if this makes sense*
memoify :: [LabelV] -> Int -> Compiler ()
memoify vivs d = queryStorage (Register d) >>= \case
  Nothing -> pure ()
  Just v -> when (v `elem` vivs) $ do
    locs <- getLocationsOf v
    case locs of
      [] -> error "nasty error, nasty"
      [Register _] -> do
        let (LLV i) = v
        emit (SStore SAVFTemps (SAK i) (SAR d))
        rememberStorage (TempMem i) v
      _ -> pure ()

-- load the value of an expression into a specific register, *if this makes sense*
registerify :: LE -> Int -> Compiler ()
registerify (LE l (EK k)) d = do
  emit (SCopy (SAR d) (SAK k))
  forgetStorage (Register d) -- don't track locations of constants, do track their clobbering
registerify (LE l (ESK name)) d = do
  emit (SCopy (SAR d) (SAName name))
  forgetStorage (Register d) -- don't track locations of constants, do track their clobbering
registerify (LE l e) d = do
  v <- getValueOf l
  already <- fmap (\case Nothing -> False; Just v' -> v == v') (queryStorage (Register d))
  when (not already) $ case e of
    EK k     -> emit (SCopy (SAR d) (SAK k))
    ESK name -> emit (SCopy (SAR d) (SAName name))
    otherwise -> do
      locs <- getLocationsOf v
      case locs of
        (Register i:_) -> emit (SCopy (SAR d) (SAR i))
        (ArgMem i:_)   -> emit (SLoad (SAR d) SAVFBase (SAK i))
        (TempMem i:_)  -> emit (SLoad (SAR d) SAVFTemps (SAK i))
        (ExpMem i:_)   -> emit (SLoad (SAR d) SAVFExpansion (SAK i))
        _ -> error ("registerify, where is the value " ++ show (LE l e) ++ ", " ++ show v ++ ", " ++ show locs)
  rememberStorage (Register d) v

-- preparedest === memoify
-- prepareoperand* === registerify


-- list of values which are 1. still needed 2. in registers 3. have no
-- other copy somewhere
spillingCandidates :: [LabelV] -> Compiler [(Int,LabelV)]
spillingCandidates vivs = (fmap catMaybes . mapM test) vivs where
  test v = do
    locs <- getLocationsOf v
    case locs of
      [] -> error "this doesn't make sense!!!"
      [Register i] -> pure (Just (i, v))
      _ -> pure Nothing
  
-- assumes a free register exists
allocateRegister :: [LabelV] -> Compiler Int
allocateRegister vivs = getFreeRegisters vivs >>= \case
  []    -> error "allocateRegister assumes at least 1 register is free"
  (i:_) -> do
    useSavedReg i
    pure i

isAlreadyThere :: LE -> Int -> Compiler Bool
isAlreadyThere (LE l e) r = do
  v <- getValueOf l
  queryStorage (Register r) >>= \case
    Nothing -> pure False
    Just v' | v' == v -> pure True
            | otherwise -> pure False
  
-- make sure n registers exist somewhere ready to use
-- assuming we cant use a list of "must avoid" registers
reserveRegistersAvoiding :: [Int] -> [LabelV] -> Int -> Compiler ()
reserveRegistersAvoiding avoids vivs n = do
  nfree <- fmap (length . (\\ avoids)) (getFreeRegisters vivs)
  when (nfree < n) $ do
    let count = n - nfree
    candidates <- fmap (filter (\(i,_) -> not (i `elem` avoids))) (spillingCandidates vivs)
    assert (length candidates >= count) $ do
      let winners = take count candidates -- dumbest possible strategy
      forM_ winners $ \(i,v) -> do
        memoify vivs i

getFreeRegisters :: [LabelV] -> Compiler [Int]
getFreeRegisters vivs = registers >>= filterM test where
  test i = queryStorage (Register i) >>= \case
    Nothing -> pure True
    Just v  -> if v `elem` vivs
      then do
        locs <- getLocationsOf v
        assert (length locs > 0) $
          pure (length locs > 1)
      else pure True

currentAndFutureVivs :: LabelE -> Compiler ([LabelV], [LabelV])
currentAndFutureVivs l = do
  LLV i <- getValueOf l
  root <- gets csGlobalTree
  let root' = substituteExpr l (LE l (EVV i)) root
  pure (activeValues root, activeValues root')

-- make sure value is either a constant or in a register, then return its symaddr
-- chooses where, if anywhere, to place the value. assumes there is a register
-- available if one is needed.
prepareOperand :: [LabelV] -> LE -> Compiler SymAddr
prepareOperand _ (LE l (EK k)) = pure (SAK k)
prepareOperand _ (LE l (ESK k)) = pure (SAName k)
prepareOperand vivs (LE l e) = do
  v <- getValueOf l
  locs <- getLocationsOf v
  case bestLocation locs of
    Just (Register i) -> pure (SAR i)
    Just (TempMem i)    -> do
      d <- allocateRegister vivs
      emit (SLoad (SAR d) SAVFTemps (SAK i))
      rememberStorage (Register d) v
      pure (SAR d)
    Just (ArgMem i)    -> do -- FIXME redundant code
      d <- allocateRegister vivs
      emit (SLoad (SAR d) SAVFBase (SAK i))
      rememberStorage (Register d) v
      pure (SAR d)
    Just (ExpMem i) -> error "prepare operand, i see it in expansion area"
    Nothing -> error ("prepareOperand failed. " ++ show l ++ " " ++ show v ++ " not found")

-- return the symaddr for the SCall instruction.
-- whose most complicated case is... the call is to a computed value which
-- is currently not in a register, and all registers are full... with values
-- that we need, and they are the only copies we have.
prepareCallee :: [LabelV] -> [LE] -> LE -> Compiler SymAddr
prepareCallee _ _ (LE l (EK k)) = pure (SAK k)
prepareCallee _ _ (LE l (ESK name)) = pure (SAName name)
prepareCallee vivs args (LE l e) = do
  v <- getValueOf l
  locs <- getLocationsOf v
  case locs of
    [] -> error "NOOOOooooooo"
    (Register i:_) -> pure (SAR i)
    (loc:_) -> do
      let avoids = [0 .. length args - 1]
      reserveRegistersAvoiding avoids vivs 1
      ds <- fmap (\\ avoids) (getFreeRegisters vivs)
      let d = case ds of [] -> error "OMG99"; (i:_) -> i
      useSavedReg d
      case loc of
        ArgMem i  -> emit (SLoad (SAR d) SAVFBase (SAK i))
        TempMem i -> emit (SLoad (SAR d) SAVFTemps (SAK i))
      pure (SAR d)


computeUnop :: Int -> LabelE -> LE -> (SymAddr -> SymAddr -> SymCode) -> Compiler ()
computeUnop d l e1 op = do
  (vivs, vivs') <- currentAndFutureVivs l
  v <- getValueOf l
  h <- isOnHand e1
  when (not h) (reserveRegistersAvoiding [] vivs 1)
  a1 <- prepareOperand [] e1
  memoify vivs' d
  emit (op (SAR d) a1)
  rememberStorage (Register d) v
  workDone l

computeBinop ::
  Int -> LabelE -> LE -> LE -> (SymAddr -> SymAddr -> SymAddr -> SymCode) -> Compiler ()
computeBinop d l e1 e2 op = do
  (vivs, vivs') <- currentAndFutureVivs l
  v <- getValueOf l
  h1 <- isOnHand e1
  h2 <- isOnHand e2
  (a1,a2) <- case (h1,h2) of
    (True,True) -> do
      a1 <- prepareOperand [] e1
      a2 <- prepareOperand [] e2
      pure (a1,a2)
    (True,False) -> do
      a1 <- prepareOperand [] e1
      reserveRegistersAvoiding (regsVal a1) vivs 1
      a2 <- prepareOperand vivs e2
      pure (a1,a2)
    (False,True) -> do
      a2 <- prepareOperand [] e2
      reserveRegistersAvoiding (regsVal a2) vivs 1
      a1 <- prepareOperand vivs e1
      pure (a1,a2)
    (False,False) -> do
      reserveRegistersAvoiding [] vivs 2
      a1 <- prepareOperand vivs e1
      a2 <- prepareOperand vivs e2
      pure (a1,a2)
  memoify vivs' d
  emit (op (SAR d) a1 a2)
  rememberStorage (Register d) v
  workDone l

regsVal :: SymAddr -> [Int]
regsVal (SAR i) = [i]
regsVal _ = []

isOnHand :: LE -> Compiler Bool
isOnHand (LE l (EK _)) = pure True
isOnHand (LE l (ESK _)) = pure True
isOnHand (LE l e) = do
  v <- getValueOf l
  locs <- fmap (filter isRegister) (getLocationsOf v)
  pure (not (null locs))
  

-- (normal) call which returns to us a value.
-- for the first N arguments, for each of the first N registers r, if r
-- does not already have the argument, then preparedest r and loan the arg
-- into r.
-- if there are more arguments, store them into expansion+1, expansion+2 ...
-- emit a call instruction, which is understood to place the return address
-- at expansion+0, forming a new virtual frame.
computeCall :: LabelE -> LE -> [LE] -> Compiler ()
computeCall l ef es = do
  v <- getValueOf l
  (vivs, _) <- currentAndFutureVivs l
  saveClobberableRegs vivs
  n <- gets csFastArgCount
  let (fastArgs,slowArgs) = splitAt n es
  -- if there are any slowArgs, get a temp register to move them all into expansion
  when (length slowArgs > 0) $ do
    reserveRegistersAvoiding [] vivs 1
    temp <- allocateRegister vivs
    forM_ (zip slowArgs [0..]) $ \(e,i) -> do
      storeExpansion e i temp
  -- fast args are passed in first four registers
  forM_ (zip fastArgs [0..]) $ \(e,i) -> do
    registerify e i
  af <- prepareCallee vivs es ef
  emit (SCall af)
  rememberStorage (Register 0) v
  workDone l

saveClobberableRegs :: [LabelV] -> Compiler ()
saveClobberableRegs vivs = do
  (clobs, _) <- clobberableOrNotRegs
  forM_ clobs (memoify vivs)

clobberableOrNotRegs :: Compiler ([Int],[Int])
clobberableOrNotRegs = do
  nregs <- gets csRegisterCount
  let topClob | even nregs = nregs `div` 2 - 1
              | otherwise  = nregs `div` 2
  pure ([0..topClob], [topClob+1 .. nregs - 1])

-- special call which recycles the current frame
computeTailCall :: LabelE -> LE -> [LE] -> Compiler ()
computeTailCall l ef es = do
  v <- getValueOf l
--  (vivs, _) <- currentAndFutureVivs l
  n <- gets csFastArgCount
  let (fastArgs,slowArgs) = splitAt n es
  vf <- getValueOf (lab ef)
  vivs <- fmap (vf:) $ mapM (getValueOf . lab) (fastArgs ++ slowArgs)
  -- fast args first, move them into target register if theyre arent already
  -- this 6 line thing needs to be moved out
  forM_ (zip fastArgs [0..]) $ \(e,i) -> do
    already <- isAlreadyThere e i
    when (not already) $ memoify vivs i
    registerify e i
  vivs <- fmap (vf:) $ mapM (getValueOf . lab) slowArgs
  memoify vivs n -- r8 in 7 fast args system
  af <- case ef of
    (LE _ (EK k)) -> pure (SAK k)
    (LE _ (ESK name)) -> pure (SAName name)
    other -> do
      registerify ef n
      pure (SAR n)
  -- if any slowArgs, begin insane process of recycling frame
  -- compiler laws do not apply past this point
  when (length slowArgs > 0) $ do
    vivs <- mapM (getValueOf . lab) slowArgs
    bumpSlowArgs (length slowArgs)
    let temp = n + 1 -- r9 in 7 fast args system
    memoify vivs temp
    forM_ (zip slowArgs [0..]) $ \(e,i) -> do
      v <- getValueOf (lab e)
      locs <- getLocationsOf v
      storeExpansionValOnly e i temp
      rememberStorage (ExpMem i) v
    forM_ (zip slowArgs [0..]) $ \(e,i) -> do
      storeInFrame e i temp
  emit SRestorePlaceholder
  emit (STailCall af) -- should be the last symcode of a block, ends compilation

computeTailQue :: Int -> LabelE -> LE -> LE -> LE -> Compiler ()
computeTailQue d l e1 e2 e3 = do
  vivs <- fmap activeValues (gets csGlobalTree)
  a1 <- prepareOperand vivs e1
  cs <- get
  let cs1 = prepareSubcompiler cs l e2
  let cs2 = prepareSubcompiler cs l e3
  let cs1' = execState (generateCode d True) cs1
  let cs2' = execState (generateCode d True) cs2
  let code1 = csCodeBuilder cs1' []
  let code2 = csCodeBuilder cs2' []
  emit (SSplit a1 code1 code2) -- final final symcode instruction
    -- actual final stuff will be done in the deepest branch
  

computeQue :: Int -> LabelE -> LE -> LE -> LE -> Compiler ()
computeQue d l e1 e2 e3 = do
  v <- getValueOf l
  (vivs, vivs') <- currentAndFutureVivs l
  scrutinee <- prepareOperand vivs e1
  cs <- get
  let cs1 = prepareSubcompiler cs l e2
  let cs2 = prepareSubcompiler cs l e3
  let cs1' = execState (generateCode d False) cs1
  let cs2' = execState (generateCode d False) cs2
  let code1 = csCodeBuilder cs1' []
  let code2 = csCodeBuilder cs2' []
  let sto1 = csStorageMap cs1'
  let sto2 = csStorageMap cs2'
  let lostValues = findLost (vivs' \\ [v]) sto1 sto2
  case lostValues of
    (_:_) -> do
      -- TODO test this
      regs <- mapM regOf lostValues
      forM_ regs (memoify vivs)
      computeQue d l e1 e2 e3
    [] -> do -- worlds are consistent!
      modify (\s -> s
        { csStorageMap = mergeStorage sto1 sto2
        , csMaxSlowArgs = max (csMaxSlowArgs cs1') (csMaxSlowArgs cs2')
        , csSavedSet = union (csSavedSet cs1') (csSavedSet cs2') })
      emit (SSplit scrutinee code1 code2)
      rememberStorage (Register d) v
      workDone l

prepareSubcompiler :: CompilerState -> LabelE -> LE -> CompilerState
prepareSubcompiler cs l e = cs
  { csLocalTree = e
  , csCodeBuilder = id
  , csGlobalTree = (substituteExpr l e (csGlobalTree cs)) }

-- which registers must have contained needed values which were lost
findLost :: [LabelV] -> Table Storage LabelV -> Table Storage LabelV -> [LabelV]
findLost vivs sto1 sto2 = filter isLost vivs where
  locs sto v = T.lookupR v sto
  isLost v = null (locs sto1 v `intersect` locs sto2 v) 

regOf :: LabelV -> Compiler Int
regOf v = do
  locs <- getLocationsOf v
  case locs of
    (Register i:_) -> pure i
    _ -> error "wwwwwhaaatttt"

mergeStorage :: Table Storage LabelV -> Table Storage LabelV -> Table Storage LabelV
mergeStorage (Table xs) (Table ys) = Table (xs `intersect` ys)

storeExpansion :: LE -> Int -> Int -> Compiler ()
storeExpansion (LE l (EK k)) i _     = emit (SStore SAVFExpansion (SAK i) (SAK k))
storeExpansion (LE l (ESK name)) i _ = emit (SStore SAVFExpansion (SAK i) (SAName name))
storeExpansion e i temp = do
  registerify e temp
  emit (SStore SAVFExpansion (SAK i) (SAR temp))

storeExpansionValOnly :: LE -> Int -> Int -> Compiler ()
storeExpansionValOnly (LE l (EK k)) i _     = pure ()
storeExpansionValOnly (LE l (ESK name)) i _ = pure ()
storeExpansionValOnly e i temp = do
  registerify e temp
  emit (SStore SAVFExpansion (SAK i) (SAR temp))

storeInFrame :: LE -> Int -> Int -> Compiler ()
storeInFrame (LE l (EK k)) i _ = emit (SStore SAVFBase (SAK i) (SAK k))
storeInFrame (LE l (ESK name)) i _ = emit (SStore SAVFBase (SAK i) (SAName name))
storeInFrame e i temp = do
  registerify e temp
  emit (SStore SAVFBase (SAK i) (SAR temp))

workDone :: LabelE -> Compiler ()
workDone l = do
  LLV i <- getValueOf l
  replaceTree l (LE l (EVV i))

replaceTree :: LabelE -> LE -> Compiler ()
replaceTree l rep = do
  tr1' <- fmap (substituteExpr l rep) (gets csGlobalTree)
  tr2' <- fmap (substituteExpr l rep) (gets csLocalTree)
  modify (\s -> s { csGlobalTree = tr1', csLocalTree = tr2' })

calleeSavedPreamble :: [Int] -> [SymCode]
calleeSavedPreamble rs = map f rs where
  f i = SStore SAVFSaves (SAK i) (SAR i)

fillInRestore :: [Int] -> [SymCode] -> [SymCode]
fillInRestore rs codes = go codes where
  restoration = map f rs where
  f i = SLoad (SAR i) SAVFSaves (SAK i)
  go [] = []
  go (SRestorePlaceholder : xs) = restoration ++ go xs
  go (SSplit x sub1 sub2 : xs) = SSplit x (go sub1) (go sub2) : go xs
  go (other : xs) = other : go xs

generateCode :: Int -> Bool -> Compiler ()
generateCode d ff = do
  localTree <- gets csLocalTree
  case seeFinal d ff localTree of
    -- final pattern, needs one of several custom finalizations
    Just fp -> case fp of
      TailBinop d l e1 e2 op -> do
        computeBinop d l e1 e2 op
        emit SRestorePlaceholder
        emit SReturn
      TailUnop d l e1 op -> do
        computeUnop d l e1 op
        emit SRestorePlaceholder
        emit SReturn
      TailValue d l e -> do
        registerify e d -- don't need to check d because this is final instruction
        emit SRestorePlaceholder
        emit SReturn
      TailFunCall _ l ef es -> computeTailCall l ef es
      TailSplit d l e1 e2 e3 -> computeTailQue d l e1 e2 e3
      MergeBinop d l e1 e2 op -> computeBinop d l e1 e2 op
      MergeUnop d l e1 op -> computeUnop d l e1 op
      MergeValue d l e -> do
        vivs <- fmap activeValues (gets csGlobalTree)
        memoify vivs d
        registerify e d
        forgetStorage (Register d) -- on merge, value in d will be merged
      MergeFunCall d l ef es -> do
        computeCall l ef es
        when (d /= 0) $ do
          emit (SCopy (SAR d) (SAR 0))
          getValueOf l >>= rememberStorage (Register d) 
    -- we have other fish to fry first
    Nothing ->
      let LE l e = nextComputation localTree in do
      case e of
        EBiop op e1 e2 -> do
          td <- selectTempDest
          computeBinop td l e1 e2 (symOp2 op)
        EUnop op e1 -> do
          td <- selectTempDest
          computeUnop td l e1 (symOp1 op)
        ELet x e1 e2 -> replaceTree l (substFreeVar x e1 e2)
        ECall ef es -> computeCall l ef es -- TODO needs testing
        EQue e1 e2 e3 -> do
          t <- selectTempDest
          computeQue t l e1 e2 e3
      generateCode d ff

-- pick where to put a temporary result, but don't move or modify anything
-- prefer free registers, but if there are none, choose an occupied one
selectTempDest :: Compiler Int
selectTempDest = do
  vivs <- fmap activeValues (gets csGlobalTree)
  frees <- getFreeRegisters vivs
  case frees of
    (i:_) -> do
      useSavedReg i
      pure i
    []    -> do
      n <- gets csRegisterCount
      pure (n - 1)

-- compiler entry point
procedure :: Int -> Int -> Proc -> [SymCode]
procedure rcount fastCount (Proc params body) =
  let body' = evalState (labelExpression body) [0..]
      sto = initialStorage fastCount params
      valmap = mkValueOf params body'
      cs = CS rcount fastCount sto body' body' valmap [] 0 id
      cs' = execState (generateCode 0 True) cs
  in if fastCount > rcount
    then error "more fast args than registers"
    else let code = csCodeBuilder cs' []
             prolog = calleeSavedPreamble (csSavedSet cs')
             saves = csSavedSet cs'
         in prolog ++ fillInRestore saves code
    -- NOT DONE, you also need to replace 

initialStorage :: Int -> [String] -> Table Storage LabelV
initialStorage fastCount params =
  let (fastParams, slowParams) = splitAt fastCount params
      fasts = zipWith (\i x -> (Register i, LLV i)) [0..] fastParams
      slows = zipWith (\i x -> (ArgMem i, LLV (fastCount + i))) [0..] slowParams
  in T.fromList (fasts ++ slows)
      
data FinalPattern =
  TailBinop Int LabelE LE LE Op2 |
  TailUnop Int LabelE LE Op1 |
  TailValue Int LabelE LE |
  TailFunCall Int LabelE LE [LE] |
  MergeBinop Int LabelE LE LE Op2 |
  MergeUnop Int LabelE LE Op1|
  MergeFunCall Int LabelE LE [LE] |
  MergeValue Int LabelE LE |
  TailSplit Int LabelE LE LE LE

type Op1 = SymAddr -> SymAddr -> SymCode
type Op2 = SymAddr -> SymAddr -> SymAddr -> SymCode

-- dest reg, main flag -> final pattern or normal problem
seeFinal :: Int -> Bool -> LE -> Maybe FinalPattern
seeFinal d True le@(LE l e) = case e of
  EVV _ -> pure $ TailValue d l le
  EK _ -> pure $ TailValue d l le
  EBV _ -> error "noooo 2"
  EPV _ _ -> pure $ TailValue d l le
  ESK _ -> pure $ TailValue d l le
  EBiop op e1 e2 | weHave e1 && weHave e2 -> pure $ TailBinop d l e1 e2 (symOp2 op)
                 | otherwise -> Nothing
  EUnop op e1 | weHave e1 -> pure $ TailUnop d l e1 (symOp1 op)
              | otherwise -> Nothing
  ELet x e1 e2 -> Nothing
  ECall ef es | weHave ef && all weHave es -> pure (TailFunCall d l ef es)
              | otherwise -> Nothing
  EQue e1 e2 e3 | weHave e1 -> pure (TailSplit d l e1 e2 e3)
                | otherwise -> Nothing
seeFinal d False le@(LE l e) = case e of
  EVV _ -> pure $ MergeValue d l le
  EK _ -> pure $ MergeValue d l le
  EBV _ -> error "noooo 2"
  EPV _ _ -> pure $ MergeValue d l le
  ESK _ -> pure $ MergeValue d l le
  EBiop op e1 e2 | weHave e1 && weHave e2 -> pure $ MergeBinop d l e1 e2 (symOp2 op)
                 | otherwise -> Nothing
  EUnop op e1 | weHave e1 -> pure $ MergeUnop d l e1 (symOp1 op)
              | otherwise -> Nothing
  ELet x e1 e2 -> Nothing
  ECall ef es | weHave ef && all weHave es -> pure (MergeFunCall d l ef es)
              | otherwise -> Nothing
  EQue e1 e2 e3 -> Nothing

weHave :: LE -> Bool
weHave (LE _ e) = case e of
  EBiop _ _ _ -> False
  EUnop _ e1 -> False
  ELet x e1 e2 -> False
  ECall ef es -> False
  EQue e1 e2 e3 -> False
  EBV _ -> error "weHave bound var?"
  _ -> True
  
substFreeVar :: String -> LE -> LE -> LE
substFreeVar x repl root = go root where
  go le@(LE l e) = case e of
    EBV y | x == y    -> repl
          | otherwise -> le
    EBiop op e1 e2 -> LE l $ EBiop op (go e1) (go e2)
    EUnop op e1 -> LE l $ EUnop op (go e1)
    ELet y e1 e2 | x == y    -> LE l $ ELet y (go e1) e2
                 | otherwise -> LE l $ ELet y (go e1) (go e2)
    ECall ef es -> LE l $ ECall (go ef) (map go es)
    EQue e1 e2 e3 -> LE l $ EQue (go e1) (go e2) (go e3)
    _ -> le

--prepare operand (an expression whose value has been computed or is a constant)
--  if the operand is a constant return the constant
--  if the value is sitting in some register return the register
--  if the value is in memory then choose a register to load it into
--    possibly save what is there, load it, update compiler, then return the register
--  otherwise explode, because we assumed the operand exists somewhere

--prepare destination (a register were about to place a result in)
--  if there is a value in the register and the value is "active" and there is
--    no other copy of it somewhere, then save it. (unless were doing a tall
--    position computation (next instruction will be to return)). update
--    compiler state


-- maybe there needs to be two prepare operands. one makes sure its in some
-- register and tells you where it ends up. could take a hint.
-- the other ensures its in a specific register, for calling conventions.
-- or to "prepare" a return value
--

instance Num E where
  fromInteger i = E (EK (fromInteger i))
  (+) = undefined
  (*) = undefined
  negate = undefined
  signum = undefined
  abs = undefined

instance IsString E where
  fromString str = E (EBV str)


data Proc = Proc [String] E
  deriving Show


add e1 e2 = E (EBiop Op2Add e1 e2)
sub e1 e2 = E (EBiop Op2Sub e1 e2)
neg e1 = E (EUnop Op1Neg e1)
param str i = E (EPV str i)
sym str = E (ESK str)
load e1 e2 = E (EBiop Op2Load e1 e2)
llet x e1 e2 = E (ELet x e1 e2)
call ef es = E (ECall ef es)
que e1 e2 e3 = E (EQue e1 e2 e3)

-- (let z = 1 + p1 in z + 3) ? (let i = 4 + 5 in glob[i]) : (p1+p2 ? p1 : p2+10)
e =
  let p1 = param "p1" 0
      p2 = param "p2" 1
  in que (llet "z" (add 1 p1) (add "z" 3))
      (llet "i" (add 4 5) (load (sym "glob") "i"))
      (que (add p1 p2) p1 (add p2 10))

ee = evalState (labelExpression e) [0..]
pr1 = Proc ["p1","p2"] e

-- let x = (p1 + p1) + (p2 + p2)
-- in (p1 ? p2 : p1) + (p2 ? p1 : p2)
e2 = let p1 = param "p1" 0
         p2 = param "p2" 1
     in llet "x" (add (add p1 p1) (add p2 p2)) (add (que p1 p2 p1) (que p2 p1 p2))
ee2 = evalState (labelExpression e2) [0..]
pr2 = Proc ["p1","p2"] e2

-- let y = p1 + p1
-- let x = (y + p2) + (p2 + p2)
-- in (y+1 ? 2+x : 2+1) + (x+1 ? y+1 : -y)
e3 = let p1 = param "p1" 0
         p2 = param "p2" 1
     in llet "y" (add p1 p1)
        (llet "x" (add (add "y" p2) (add p2 p2))
         (add
            (que (add "y" 1) (add 2 "x") (add 2 1))
            (que (add "x" 1) (add "y" 1) (neg "y"))))
ee3 = evalState (labelExpression e3) [0..]
pr3 = Proc ["p1","p2"] e3

--e4 = add 2 3
{-e4 = call (sym "sine")
  [sym "foo"
  ,param "p1" 0
  ,param "p2" 1
  ,37
  ,45
  ,param "p2" 1] -}
--e4 = que (param "p2" 1) (add (add 1 2) (param "p1" 0)) (param "p1" 0)
e4 = add (que (que 0 (call (sym "f") [9,9,9]) 2) (que 3 4 5) (que 6 7 8)) 1
--e4 = add (call (sym "f") [99,99,add 2 2,99,88]) 3
ee4 = evalState (labelExpression e4) [0..]
pr4 = Proc ["p1","p2"] e4

-- def sum(ptr, n, a)
--   n == 0 ? a : sum(ptr, n-1, a + ptr[n-1])
e5 = que (param "n" 1)
  (param "a" 2)
  (llet "n'" (sub (param "n" 1) 1)
    (call (sym "sum")
      [ param "ptr" 0
      , "n'"
      , add (param "a" 2) (load (param "ptr" 0) "n'") ]))
ee5 = evalState (labelExpression e5) [0..]
pr5 = Proc ["ptr","n","a"] e5

-- let x = 3 ? y + 2 : -(let z = 9 in z) in -(x + x)
e6 = llet "x"
  (que 3
    (add (param "y" 0) 2)
    (neg (llet "z" 9 "z")))
  (neg (add "x" "x"))
pr6 = Proc ["y"] e6


e7 = llet "x" (add 2 2) 
  (llet "y" (add 1 1)
     (call (sym "f") ["y","x","y","x",param "z" 0]))
pr7 = Proc ["z"] e7

-- let x = 3 ? sin(1) : sin(1)+1
-- in -x
e8 = llet "x"
      (que 3 (call (sym "sin") [1]) (add (call (sym "sin") [1]) 1))
      (add (param "y" 0) (neg "x"))
pr8 = Proc ["y"] e8

{-
e9 = llet "x" (add 2 1)
 (llet "y" (call (load (sym "obj") (sym "method"))
    [ add (add (add "x" 99) (add 45 16)) "x"
    , add (add 1 2) (add (add 0 0) (add 0 0))
    , add 0 0]) (neg "y"))
-}
e9 = llet "x" (add 2 1)
 (call (load (sym "obj") (sym "method"))
    [ add (add (add "x" 99) (add 45 16)) "x"
    , add (add 1 2) (add (add 0 0) (add 0 0))
    , add 0 0])
pr9 = Proc [] e9
