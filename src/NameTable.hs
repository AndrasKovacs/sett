
{-| Mapping from raw names -}

module NameTable where

import qualified Data.ByteString      as B
import qualified Data.HashMap.Strict  as HM

import Common
import qualified Syntax    as S
import qualified Values    as V

data Entry
  = Top Lvl S.Ty {-# unpack #-} V.GTy ~V.Val -- ^ Level, type, type val, value
  | Local Lvl {-# unpack #-} V.GTy           -- ^ Level, type val

type NameTable    = HM.HashMap B.ByteString Entry
type NameTableArg = (?nameTable :: NameTable)

nameTable :: (NameTableArg => a) -> (NameTableArg => a)
nameTable a = seq ?nameTable a
{-# inline nameTable #-}

lookupBS :: B.ByteString -> NameTable -> Maybe Entry
lookupBS = HM.lookup

lookup :: Span -> NameTable -> Maybe Entry
lookup x = HM.lookup (spanToBs x)

insert :: Bind -> Entry -> NameTable -> NameTable
insert x entry tbl = case x of
  Bind x   -> HM.insert (spanToBs x) entry tbl
  DontBind -> tbl
