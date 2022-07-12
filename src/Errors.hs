
module Errors where

import Syntax
import Common
import qualified Presyntax as P

data Error
  = UnifyError Tm Tm
  | NameNotInScope P.Name
  | NoSuchField P.Name
  | NoSuchArgument P.Name
  | IcitMismatch Icit Icit
  | NoNamedLambdaInference
  | ExpectedSg Tm
  deriving Show

data ElabError = ElabError Locals P.Tm Error
