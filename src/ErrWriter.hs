
{-# language UnboxedTuples #-}

{-| The same thing as @WriterT All IO a@, implemented more efficiently. -}

module ErrWriter where

import Control.Monad
import GHC.Exts
import GHC.Types

newtype ErrWriter a = ErrWriter# {unErrWriter# :: State# RealWorld -> (# a, Int#, State# RealWorld #)}

instance Functor ErrWriter where
  fmap f (ErrWriter# g) = ErrWriter# \s -> case g s of (# a, e, s #) -> let b = f a in (# b, e, s #)
  {-# inline fmap #-}

instance Applicative ErrWriter where
  pure a = ErrWriter# \s -> (# a, 1#, s #)
  {-# inline pure #-}
  (<*>) (ErrWriter# f) (ErrWriter# a) = ErrWriter# \s -> case f s of
    (# f, e, s #) -> case a s of
      (# a, e', s #) -> let b = f a in (# b, andI# e e', s #)
  {-# inline (<*>) #-}

instance Monad ErrWriter where
  return = pure
  {-# inline return #-}
  ErrWriter# f >>= g = ErrWriter# \s -> case f s of
    (# a, e, s #) -> case unErrWriter# (g a) s of
      (# b, e', s #) -> (# b, andI# e e', s #)
  {-# inline (>>=) #-}

liftIO :: IO a -> ErrWriter a
liftIO (IO f) = ErrWriter# \s -> case f s of (# s, a #) -> (# a, 1#, s #)
{-# inline liftIO #-}

writeErr :: ErrWriter ()
writeErr = ErrWriter# \s -> (# (), 0#, s #)
{-# inline writeErr #-}

-- | Capture the error output of an action in the return value. Reset the error
--   value to success.
catch :: ErrWriter a -> ErrWriter (a, Bool)
catch (ErrWriter# f) = ErrWriter# \s -> case f s of
  (# a, e, s #) -> let b = isTrue# e in (# (a, b), 1#, s #)
{-# inline catch #-}

liftIOBool :: IO Bool -> ErrWriter ()
liftIOBool act = do
  b <- liftIO act
  unless b writeErr
{-# inline liftIOBool #-}

run :: ErrWriter a -> IO (a, Bool)
run (ErrWriter# f) = IO \s -> case f s of
  (# a, e, s #) -> let b = isTrue# e in (# s, (a, b) #)
{-# inline run #-}
