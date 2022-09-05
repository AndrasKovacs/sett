{-# options_ghc -funbox-strict-fields #-}

module TopCxt where

import IO
import qualified Data.Array.Dynamic.L as ADL
import qualified Data.Ref.F           as RF
import qualified Data.Array.LI        as LI

import Common
import qualified Presyntax as P
import qualified Syntax    as S

--------------------------------------------------------------------------------

data TopEntry
  = TEDef P.Name S.Ty S.Tm MetaVar  -- ^ Name, type, definition, marker for frozen metas.
  | TEPostulate P.Name S.Ty MetaVar -- ^ Type, marker for frozen metas.

type TopInfo    = ADL.Array TopEntry
type TopInfoArg = (?topInfo :: TopInfo)

topInfo :: TopInfo
topInfo = runIO $ ADL.empty
{-# noinline topInfo #-}

readTopInfo :: Lvl -> IO TopEntry
readTopInfo x = ADL.read topInfo (coerce x)

frozen :: RF.Ref MetaVar
frozen = runIO $ RF.new 0
{-# noinline frozen #-}

readFrozen :: IO MetaVar
readFrozen = RF.read frozen

writeFrozen :: MetaVar -> IO ()
writeFrozen = RF.write frozen

-- | Get all top-level names as strings.
topNames :: TopInfoArg => IO (LI.Array String)
topNames = do
  entries <- ADL.freeze ?topInfo
  let go = \case
        TEDef x _ _ _ -> spanToString x
        TEPostulate x _ _ -> spanToString x
  pure $! LI.map go entries
