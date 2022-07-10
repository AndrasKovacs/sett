{-# language UnboxedTuples #-}

module Common (
    module Common
  , coerce ) where

import Data.List
import GHC.Exts
import Data.Bits
import Data.Flat
import Data.Time.Clock

import qualified Data.ByteString as B
import qualified Data.ByteString.Internal as B
import qualified FlatParse.Stateful as FP

-- Debug printing, toggled by "debug" cabal flag
--------------------------------------------------------------------------------

-- define DEBUG
#ifdef DEBUG
type Dbg = HasCallStack

debug :: [String] -> IO ()
debug strs = U.io $ putStrLn (intercalate " | " strs ++ " END")

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

-- | Strict `fmap`.
(<$!>) :: Monad f => (a -> b) -> f a -> f b
(<$!>) f fa = do
  a <- fa
  pure $! f a
infixl 4 <$!>
{-# inline (<$!>) #-}

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

data Icit = Impl | Expl deriving (Eq, Show)

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

lvlToIx :: Lvl -> Lvl -> Ix
lvlToIx (Lvl envl) (Lvl x) = Ix (envl - x - 1)
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

srcToByteString :: Src -> B.ByteString
srcToByteString (File _ bs)      = bs
srcToByteString (Interactive bs) = bs

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
  deriving Show via Hide Span

pattern Span :: Pos -> Pos -> Span
pattern Span x y <- ((\(Span# src x y) -> (Pos src x, Pos src y)) -> (x, y)) where
  Span (Pos src x) (Pos src' y)
    | src == src' && x <= y = Span# src x y
    | otherwise             = impossible
{-# complete Span #-}

spanToByteString :: Span -> B.ByteString
spanToByteString (Span (Pos src i) (Pos _ j)) =
  let bstr = srcToByteString src
      i'   = B.length bstr - coerce i   -- Pos counts backwards from the end of the string
      j'   = B.length bstr - coerce j
  in B.take (j' - i') (B.drop i' bstr)

spanToString :: Span -> String
spanToString s = FP.unpackUTF8 (spanToByteString s)


-- -- Names in core syntax
-- --------------------------------------------------------------------------------

-- data Name
--   = NUnused                    -- ^ Unused binder (underscore in surface syntax).
--   | NX                         -- ^ Generic non-informative name. It will be usually
--                                --   un-shadowed in pretty printing.
--   | NSpan {-# unpack #-} Span  -- ^ Name which comes from user source.

-- instance Show Name where
--   showsPrec d NUnused   acc = '_':acc
--   showsPrec d NX        acc = 'x':acc
--   showsPrec d (NSpan x) acc = showsPrec d x acc


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
