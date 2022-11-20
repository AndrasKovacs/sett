
module Configuration where

-- TODO: benchmark these!

-- | Meta solutions smaller than this size (in terms of syntax AST nodes) which contain at most one
--   metavar, will be inlined.
inlineMaxSize :: Int
inlineMaxSize = 30

-- | The number of simplification passes we do on each top-level block. Each pass inlines linear metas or metas
--   with small solutions.
simplificationPasses :: Int
simplificationPasses = 3

-- | How many times can we backtrack from an unfolding in unification and conversion checking.
conversionSpeculation :: Int
conversionSpeculation = 3
