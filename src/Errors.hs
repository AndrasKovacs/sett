
module Errors where

import Control.Exception

import Syntax
import Common
import Values
import qualified Presyntax as P

data UnifyEx = CantUnify | FrozenSolution | FlexSolution
  deriving (Eq, Show)
instance Exception UnifyEx

data Error
  = UnifyError Val Val
  | NameNotInScope P.Name
  | NoSuchField P.Name
  | NoNamedImplicitArg P.Name
  | IcitMismatch Icit Icit
  | NoNamedLambdaInference
  | ExpectedSg Tm
  | ExpectedFunOrForall Val -- inferred type
  | GenericError String

data ErrorInCxt = ErrorInCxt Locals P.Tm Error

instance Show ErrorInCxt where
  show = uf

instance Exception ErrorInCxt
