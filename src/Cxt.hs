
module Cxt (
  module Cxt.Types,
  module Cxt.Extension,
  askCxt ) where

import Cxt.Types
import Cxt.Extension

askCxt :: CxtArg Cxt
askCxt = Cxt ?lvl ?env ?locals ?nameTable
{-# inline askCxt #-}
