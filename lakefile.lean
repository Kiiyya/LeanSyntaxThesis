import Lake
open Lake DSL

package "Syntax" where
  version := v!"0.1.0"

@[default_target]
lean_lib Syntax where
  require aesop from git "https://github.com/leanprover-community/aesop" @ "v4.30.0-rc2"
  require Qq from git "https://github.com/leanprover-community/quote4" @ "v4.30.0-rc2"
  require "leanprover-community" / "mathlib" @ "git#v4.30.0-rc2"
