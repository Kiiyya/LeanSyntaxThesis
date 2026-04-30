
import Lean

open Lean Meta Elab Term

initialize registerTraceClass `stx.debug

initialize registerTraceClass `stx.isQ
initialize registerTraceClass `stx.red
initialize registerTraceClass `stx.isDefEq
-- initialize registerTraceClass `stx.elabProofs
-- initialize registerTraceClass `stx.elab
