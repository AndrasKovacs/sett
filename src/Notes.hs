{-# language ImplicitParams #-}

module Notes where


-- f :: (?n :: Int) => Int
-- f = ?n

newtype F a b = F {unF :: (?arg :: a) => b}

app :: F a b -> a -> b
app (F f) a = let ?arg = a in f

f :: F Int (F Int (F Int Int))
f = F (F (F ?arg))

g :: Int
g = f `app` 0 `app` 1 `app` 20


-- newtype F = F {unF :: ((?n :: Int) => Int)}

-- app :: F -> Int -> Int
-- app f n = let ?n = n; ?n = 0 in unF f

-- f = F ?n

-- g :: Int
-- g = let
--   ?n = 100
--   in f
