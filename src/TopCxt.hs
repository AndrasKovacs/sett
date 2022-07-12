
module TopCxt where

import IO
import qualified Data.Array.Dynamic.L as ADL
import qualified Data.ByteString      as B
import qualified Data.HashMap.Strict  as HM
import qualified Data.Ref.F           as RF
import qualified Data.Ref.L           as RL

import Common
import qualified Presyntax as P
import qualified Syntax    as S
import qualified Values    as V

--------------------------------------------------------------------------------

data TopEntry
  = TEDef P.Name S.Ty S.Tm MetaVar -- ^ Name, type, definition, marker for frozen metas.
  | TEPostulate S.Ty MetaVar       -- ^ Type, marker for frozen metas.

type TopInfo = ADL.Array TopEntry

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
