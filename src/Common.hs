{-# language UnboxedTuples #-}

module Common (
    module Common
  , module Control.Monad
  , catch
  , coerce
  ) where


import Control.Exception
import Control.Monad
import Data.Bits
import Data.Flat
import Data.List
import Data.Time.Clock
import Debug.Trace
import GHC.Exts
import GHC.Stack
import IO

import qualified Data.ByteString as B
import qualified Data.ByteString.Internal as B
import qualified Data.Ref.L as RL
import qualified FlatParse.Stateful as FP


-- Debug printing, toggled by "debug" CPP flag or by a runtime toggle
--------------------------------------------------------------------------------

debugToggle :: RL.Ref Bool
debugToggle = runIO $ RL.new True
{-# noinline debugToggle #-}

enableDebug :: IO ()
enableDebug = RL.write debugToggle True

disableDebug :: IO ()
disableDebug = RL.write debugToggle False

readDebugToggle :: IO Bool
readDebugToggle = RL.read debugToggle

#define DEBUG
#ifdef DEBUG
type Dbg = HasCallStack

debug :: [String] -> IO ()
debug strs = do
  RL.read debugToggle >>= \case
    True -> traceM (intercalate " | " strs ++ " END")
    False -> pure ()

debugging :: IO () -> IO ()
debugging act = act
#else
type Dbg = () :: Constraint

debug :: [String] -> IO ()
debug strs = pure ()
{-# inline debug #-}

debugging :: IO () -> IO ()
debugging _ = pure ()
#endif

debug' :: [String] -> IO ()
debug' strs = putStrLn (intercalate " | " strs ++ " END")

debugging' :: IO () -> IO ()
debugging' act = act

-- Configuration
--------------------------------------------------------------------------------

-- | How many times can we backtrack in unification/conversion checking.
conversionSpeculation :: Int
conversionSpeculation = 3

-- Misc
--------------------------------------------------------------------------------

-- | Abbreviation for `undefined`.
uf :: Dbg => a
uf = undefined
{-# noinline uf #-}

-- | Strict pair construction.
(//) :: a -> b -> (a, b)
a // b = (a, b)
infix 2 //
{-# inline (//) #-}

impossible :: Dbg => a
impossible = error "impossible"
{-# noinline impossible #-}

-- | Pointer equality.
ptrEq :: a -> a -> Bool
ptrEq !x !y = isTrue# (reallyUnsafePtrEquality# x y)
{-# inline ptrEq #-}

-- | Count trailing zeros.
ctzInt :: Int -> Int
ctzInt (I# n) = I# (word2Int# (ctz# (int2Word# n)))
{-# inline ctzInt #-}

-- | Strict function application that associates to the left. A more convenient
--   version of `($!)`.
($$!) :: (a -> b) -> a -> b
($$!) f x = f x
infixl 0 $$!
{-# inline ($$!) #-}

-- | Strict `(<*>)`.
(<*!>) :: Monad f => f (a -> b) -> f a -> f b
(<*!>) ff fa = do
  f <- ff
  a <- fa
  pure $! f a
infixl 4 <*!>
{-# inline (<*!>) #-}

-- | Hiding things in printing using a newtype wrapper.
newtype Hide a = Hide a deriving (Eq)

instance Show (Hide a) where showsPrec _ x acc = acc
-- deriving instance Show a => Show (Hide a)


-- Icitness
--------------------------------------------------------------------------------

newtype Icit = Icit# Int deriving Eq
pattern Impl = Icit# 0
pattern Expl = Icit# 1
{-# complete Impl, Expl #-}

instance Show Icit where
  show Impl = "Impl"
  show Expl = "Expl"

icit :: Icit -> a -> a -> a
icit Impl x y = x
icit Expl x y = y
{-# inline icit #-}


-- De Bruijn indices, levels, metavariables
--------------------------------------------------------------------------------

newtype Ix = Ix {unIx :: Int}
  deriving (Eq, Ord, Show, Num, Enum, Bits) via Int

newtype Lvl = Lvl {unLvl :: Int}
  deriving (Eq, Ord, Show, Num, Enum, Bits, Flat) via Int

type LvlArg = (?lvl :: Lvl)
type TopLvlArg = (?topLvl :: Lvl)

-- | Ordinary metavariable.
newtype MetaVar = MkMetaVar Int
  deriving (Eq, Ord, Num, Flat) via Int

instance Show MetaVar where
  showsPrec _ (MkMetaVar x) acc = '?': showsPrec 0 x acc

-- | Metavariable for universes (Set/Prop).
newtype UVar = MkUVar Int
  deriving (Eq, Ord, Num, Flat) via Int

instance Show UVar where
  showsPrec _ (MkUVar x) acc = '?': showsPrec 0 x acc

lvlToIx :: LvlArg => Lvl -> Ix
lvlToIx (Lvl x) = Ix (coerce ?lvl - x - 1)
{-# inline lvlToIx #-}


-- Source descriptors, positions, spans
--------------------------------------------------------------------------------

-- | Describes a source bytestring such that a position can point into it.
data Src
  = File FilePath B.ByteString -- ^ Concrete source file.
  | Interactive B.ByteString   -- ^ Interactive (REPL) input. TODO: more data here.

instance Show Src where
  show (File fp _) = "File " ++ fp
  show (Interactive _) = "Interactive"

srcToBs :: Src -> B.ByteString
srcToBs (File _ bs)      = bs
srcToBs (Interactive bs) = bs

-- | Equality of bytestrings by reference, used for sanity checks.
samePtr :: B.ByteString -> B.ByteString -> Bool
samePtr x y = case B.toForeignPtr x of
  (x, _, _) -> case B.toForeignPtr y of
    (y, _, _) -> x == y
{-# inline samePtr #-}

-- | Equality of sources only checks that underlying bytestrings have the same
--   underlying data.
instance Eq Src where
  File _ s      == File _ s'      = samePtr s s'
  Interactive s == Interactive s' = samePtr s s'
  _             == _              = False

-- | Source position. We decorate raw terms with this.
data Pos = Pos Src FP.Pos
  deriving Show via Hide Pos
  deriving Eq

rawPos :: Pos -> FP.Pos
rawPos (Pos _ p) = p

instance Ord Pos where
  compare (Pos src i) (Pos src' i')
    | src == src' = compare i i'
    | otherwise   = impossible

  (<) (Pos src i) (Pos src' i')
    | src == src' = i < i'
    | otherwise   = impossible

  (<=) (Pos src i) (Pos src' i')
    | src == src' = i <= i'
    | otherwise   = impossible

-- | Source span. The left position must not be larger than the right one.
data Span = Span# Src FP.Pos FP.Pos
  -- deriving Show via Hide Span

instance Show Span where
  show = spanToString

leftPos :: Span -> Pos
leftPos (Span l _) = l
{-# inline leftPos #-}

rightPos :: Span -> Pos
rightPos (Span _ r) = r
{-# inline rightPos #-}

pattern Span :: Pos -> Pos -> Span
pattern Span x y <- ((\(Span# src x y) -> (Pos src x, Pos src y)) -> (x, y)) where
  Span (Pos src x) (Pos src' y)
    | src == src' && x <= y = Span# src x y
    | otherwise             = impossible
{-# complete Span #-}

spanToBs :: Span -> B.ByteString
spanToBs (Span (Pos src i) (Pos _ j)) =
  let bstr = srcToBs src
      i'   = B.length bstr - coerce i   -- Pos counts backwards from the end of the string
      j'   = B.length bstr - coerce j
  in B.take (j' - i') (B.drop i' bstr)

instance Eq Span where
  x == y = spanToBs x == spanToBs y

spanToString :: Span -> String
spanToString s = FP.unpackUTF8 (spanToBs s)

-- Names in core syntax
--------------------------------------------------------------------------------

data Bind
  = Bind Span
  | DontBind

instance Show Bind where
  showsPrec _ (Bind x)  acc = showsPrec 0 x acc
  showsPrec _  DontBind acc = '_':acc

data Name
  = NUnused                    -- ^ Unused binder (underscore in surface syntax).
  | NSpan {-# unpack #-} Span  -- ^ Name which comes from user source.
  | NLit String                -- ^ Literal string which does not come from source.
  deriving Eq

nx, ny, nz, na, nb, nc, nf, ng, nh :: Name
nx = NLit "x"
ny = NLit "y"
nz = NLit "z"
np = NLit "p"
nq = NLit "q"
na = NLit "A"
nb = NLit "B"
nc = NLit "C"
nf = NLit "f"
ng = NLit "g"
nh = NLit "h"

instance Show Name where
  showsPrec d NUnused   acc = '_':acc
  showsPrec d (NSpan x) acc = spanToString x++acc
  showsPrec d (NLit s)  acc = s ++ acc

bindToName :: Bind -> Name
bindToName = \case
  Bind x   -> NSpan x
  DontBind -> NUnused

pick :: Name -> Name -> Name
pick x y = case x of
  NUnused -> case y of
    NUnused -> nx
    y -> y
  x -> x

--------------------------------------------------------------------------------

-- | Error-like values used during partial substitution.
data Magic
  = Undefined
  | Nonlinear
  | MetaOccurs
  deriving (Eq, Show)

instance Exception Magic

data SP = S | P deriving (Eq, Show)

--------------------------------------------------------------------------------

-- TODO: bit-pack UnifyState and ConvState

data UnfoldOpt = UnfoldMetas | UnfoldEverything | UnfoldNothing
  deriving (Eq, Show)

type UnfoldOptArg = (?unfoldOpt :: UnfoldOpt)

data UnifyState
  = USRigid Int  -- ^ Starting state from which speculation can be initiated.
                 --   The `Int` contains the number of shots we get at speculation. We
                 --   can solve arbitrary metas.
  | USFlex       -- ^ We're in this state during speculation. We can't compute unfoldings
                 --   in this state, and can only solve irrelevant metas.
  | USFull       -- ^ We're in this state after we've exhausted the speculation budget.
                 --   We immediately compute all unfoldings and we can solve metas.
  | USIrrelevant -- ^ We're in this state when we unify inside irrelevant values.
                 --   We can only solve irrelevant metas. All failure is caught and
                 --   converted to success.
  deriving (Eq, Show)

type UnifyStateArg = (?unifyState :: UnifyState)

data ConvState
  = CSRigid Int -- ^ Starting state from which speculation can be initiated.
                --   The `Int` contains the number of shots we get at speculation.
  | CSFlex      -- ^ We're in this state during speculation. We can't compute unfoldings.
  | CSFull      -- ^ We're in this state we've exhausted the speculation budget. We immediately
                --   compute all unfoldings.
  deriving (Eq, Show)

-- Timing
--------------------------------------------------------------------------------

-- | Time an IO computation. Result is forced to whnf.
timed :: IO a -> IO (a, NominalDiffTime)
timed a = do
  t1  <- getCurrentTime
  res <- a
  t2  <- getCurrentTime
  let diff = diffUTCTime t2 t1
  pure (res, diff)
{-# inline timed #-}

-- | Time a lazy pure value. Result is forced to whnf.
timedPure :: a -> IO (a, NominalDiffTime)
timedPure ~a = do
  t1  <- getCurrentTime
  let res = a
  t2  <- getCurrentTime
  let diff = diffUTCTime t2 t1
  pure (res, diff)
{-# noinline timedPure #-}

-- | Time a lazy pure value. Result is forced to whnf.
timedPure_ :: a -> IO NominalDiffTime
timedPure_ ~a = do
  t1  <- getCurrentTime
  seq a $ do
    t2  <- getCurrentTime
    let diff = diffUTCTime t2 t1
    pure diff
{-# noinline timedPure_ #-}

--------------------------------------------------------------------------------
