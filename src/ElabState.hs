
module ElabState where

import IO
import qualified Data.Array.Dynamic.L as ADL
import qualified Data.Ref.F           as RF

import Common
import Values
import qualified Values as V
import qualified Syntax as S
import qualified Presyntax as P


-- Metacontext
--------------------------------------------------------------------------------

type OccursCache = RF.Ref MetaVar

data MetaEntry
  = MEUnsolved {-# unpack #-} GTy                -- ^ Type
  | MESolved OccursCache Val {-# unpack #-} GTy  -- ^ Occurs check cache, value, type

type MetaCxt = ADL.Array MetaEntry

metaCxt :: ADL.Array MetaEntry
metaCxt = runIO ADL.empty
{-# noinline metaCxt #-}

nextMeta :: IO Lvl
nextMeta = coerce <$!> ADL.size metaCxt

readMeta :: MetaVar -> IO MetaEntry
readMeta (MkMetaVar i) = ADL.read metaCxt i
{-# inline readMeta #-}

newMeta :: GTy -> IO MetaVar
newMeta a = do
  s <- ADL.size metaCxt
  ADL.push metaCxt (MEUnsolved a)
  pure (MkMetaVar s)
{-# inline newMeta #-}

solve :: MetaVar -> V.Val -> V.GTy -> IO ()
solve x tv a = do
  ADL.unsafeRead metaCxt (coerce x) >>= \case
    MESolved{} -> impossible
    MEUnsolved mask -> do
      cache <- RF.new (-1)
      ADL.write metaCxt (coerce x) (MESolved cache tv a)


-- Top-level elaboration context
--------------------------------------------------------------------------------

data TopEntry
  = TEDef P.Name S.Ty S.Tm MetaVar -- ^ Name, type, definition, marker for frozen metas.
  | TEPostulate S.Ty V.GTy MetaVar -- ^ Type, type val, marker for frozen metas.

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
