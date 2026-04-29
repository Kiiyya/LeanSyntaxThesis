import Aesop
import Qq
import Lean
import Syntax.Erased
import Syntax.Wellformed
import Syntax.AllTogether
import Syntax.Elab

set_option pp.fieldNotation.generalized false

open Notation

#check Ty(Type -> Type)
