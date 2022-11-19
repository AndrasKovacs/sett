
module ElabState where

import IO
import qualified Data.Array.Dynamic.L as ADL
import qualified Data.Ref.F           as RF
import qualified Data.Ref.L           as RL

import Common
import Values
import NameTable
import qualified Values as V
import qualified Syntax as S
import qualified Presyntax as P
-- import Optimize

-- Metacontext
--------------------------------------------------------------------------------

type OccursCache = RF.Ref MetaVar

data MetaEntry
  -- ^ Type, locals
  = MEUnsolved Ty S.Locals
  -- ^ Occurs check cache, term solution, value, type, inlinable
  | MESolved OccursCache S.Tm Val Ty Bool

type MetaCxt = ADL.Array MetaEntry

metaCxt :: ADL.Array MetaEntry
metaCxt = runIO ADL.empty
{-# noinline metaCxt #-}

nextMeta :: IO MetaVar
nextMeta = coerce <$!> ADL.size metaCxt

readMeta :: MetaVar -> IO MetaEntry
readMeta (MkMetaVar i) = ADL.read metaCxt i
{-# inline readMeta #-}

writeMeta :: MetaVar -> MetaEntry -> IO ()
writeMeta (MkMetaVar i) e = ADL.write metaCxt i e
{-# inline writeMeta #-}

newMeta :: S.LocalsArg => Ty -> IO MetaVar
newMeta a = do
  s <- ADL.size metaCxt
  debug ["NEW META", show s]
  ADL.push metaCxt (MEUnsolved a ?locals)
  pure (MkMetaVar s)
{-# inline newMeta #-}

-- | Trim the size of the metacontext to `Lvl`.
resetMetaCxt :: MetaVar -> IO ()
resetMetaCxt size = do
  currSize <- nextMeta
  if size < currSize then ADL.pop metaCxt >> resetMetaCxt size
                     else pure ()

unsolvedMetaType :: MetaVar -> IO V.Ty
unsolvedMetaType x = readMeta x >>= \case
  MEUnsolved a _ -> pure a
  _              -> impossible

metaType :: MetaVar -> IO V.Ty
metaType x = readMeta x >>= \case
  MEUnsolved a _     -> pure a
  MESolved _ _ _ a _ -> pure a

countSolvedMetas :: IO Int
countSolvedMetas = do
  ADL.foldl' (\acc -> \case
                 MEUnsolved{} -> acc
                 MESolved{} -> acc+1) 0 metaCxt

-- Top-level elaboration context
--------------------------------------------------------------------------------

data TopEntry
  = TEDef P.Name S.Ty S.Tm MetaVar        -- ^ Name, type, definition, marker for frozen metas.
  | TEPostulate P.Name S.Ty V.Ty MetaVar -- ^ Type, type val, marker for frozen metas.

type TopInfo = ADL.Array TopEntry
type TopInfoArg = (?topInfo :: TopInfo)

topInfo :: TopInfo
topInfo = runIO $ ADL.empty
{-# noinline topInfo #-}

readTopInfo :: Lvl -> IO TopEntry
readTopInfo x = ADL.read topInfo (coerce x)

pushTop :: TopEntry -> IO ()
pushTop = ADL.push topInfo

topSize :: IO Lvl
topSize = coerce <$!> ADL.size topInfo

-- Frozen metas
--------------------------------------------------------------------------------

frozen :: RF.Ref MetaVar
frozen = runIO $ RF.new 0
{-# noinline frozen #-}

-- | Freeze all current metas, return size of metacontext.
freezeMetas :: IO MetaVar
freezeMetas = do
  frz <- nextMeta
  RF.write frozen frz
  pure frz

isFrozen :: MetaVar -> IO Bool
isFrozen x = do
  frz <- RF.read frozen
  pure $! x < frz

-- Source of code being elaborated
--------------------------------------------------------------------------------

elabSource :: RL.Ref (Maybe Src)
elabSource = runIO $ RL.new Nothing
{-# noinline elabSource #-}

readElabSource :: IO (Maybe Src)
readElabSource = RL.read elabSource

writeElabSource :: Maybe Src -> IO ()
writeElabSource msrc = RL.write elabSource msrc

-- Top-level nametable
--------------------------------------------------------------------------------

topNameTable :: RL.Ref NameTable
topNameTable = runIO $ RL.new mempty
{-# noinline topNameTable #-}

--------------------------------------------------------------------------------

reset :: IO ()
reset = do
  ADL.clear metaCxt
  RF.write frozen 0
  ADL.clear topInfo
  writeElabSource Nothing
  RL.write topNameTable mempty
