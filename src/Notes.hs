
module Notes where

-- import Data.Kind
-- import GHC.TypeLits
-- import Unsafe.Coerce

-- f :: (?lvl :: Bool, ?foo :: Bool) => Bool
-- f = ?lvl
-- {-# noinline f #-}


-- g :: Bool -> Bool -> Bool
-- g ~x ~y = let ?foo = x; ?lvl = y in f
-- {-# noinline g #-}

abs :: ((?x :: Int, ?y :: Int) => Int) -> ((?x :: Int, ?y :: Int) => Int)
abs f = seq ?x (seq ?y f)


-- h :: ((?x :: Int, ?y :: Int) => Int) -> Int -> Int
-- h ~f ~x = let ?x = x + 10; ?y = x + 20 in f

-- h2 :: (Int -> Int -> Int) -> Int -> Int
-- h2 ~f ~x = let x' = x + 10; y' = x + 20 in f x' y'




-- foo :: Bool ->  Bool -> Bool
-- foo x y = False
-- {-# noinline foo #-}



-- class IP (s :: Symbol) (a :: Type) | s -> a where
--   get :: a

-- newtype Abs s a b = Abs (IP s a => b)

-- def :: forall s a b. a -> Abs s a b -> b
-- def a f = (unsafeCoerce f :: a -> b) a
-- {-# inline def #-}

-- type IntArg = IP "lvl" Int

-- f :: IntArg => Int
-- f = get @"lvl" + 300
-- {-# noinline f #-}

-- g :: Int -> Int
-- g x = def @"lvl" x $ Abs f
-- {-# noinline g #-}


-- f2 :: Int -> Int
-- f2 x = x + 300
-- {-# noinline f2 #-}

-- g2 :: Int -> Int
-- g2 x = let y = x in f2 y
-- {-# noinline g2 #-}

-- f3 :: (?lvl::Int) => Int
-- f3 = ?lvl + 300
-- {-# noinline f3 #-}

-- g3 :: Int -> Int
-- g3 x = let ?lvl = x in f3
-- {-# noinline g3 #-}

-- f4 :: (?lvl::Int, ?mallac::Int) => Int
-- f4 = ?lvl + 300
-- {-# noinline f4 #-}

-- g4 :: Int -> Int -> Int
-- g4 x y = let ?lvl = x; ?mallac = y in f4
-- {-# noinline g4 #-}
