import Lean
import Aesop
import Qq
import Syntax.Elim.Shapeless

set_option pp.fieldNotation.generalized false
set_option linter.unusedVariables false

namespace ChooseExample

open Notation
open Con Ty Tm Subst Var

def choose (X : Type) (Y : Type) : Bool -> Type :=
  fun c => Bool.rec (motive := fun _ => Type) X Y c

def pick (A B : Type) : A -> choose A B false :=
  fun a : A => a


abbrev Γ : Con := .nil; .U; .U
-- some helpers:
def X  : Tm Γ           .U           := .var (.vs .vz)
def Y  : Tm Γ           .U           := .var .vz
def x  : Tm (Γ; .El X) (.El X[.wki]) := .var .vz

/- Reminder:
```
def Tm.elimSum (Mot : Ty (Γ; A+B))
  (leftM  : Tm (Γ; A) Mot[wki ;; (.left  (.var .vz)     : Tm (Γ; A) (A[wki] + B[wki]))])
  (rightM : Tm (Γ; B) Mot[wki ;; (.right (.var .vz)     : Tm (Γ; B) (A[wki] + B[wki]))])
  (t : Tm Γ (A + B)) : Tm Γ Mot[.apply t]
```
-/

def chooseStx : Tm Γ (.Pi (Sum Unit Unit) U) :=
  .lam <|
    Tm.elimSum (Γ := Γ; .Sum .Unit .Unit) (A := .Unit) (B := .Unit)
      .U
      X[.wki][.wki]
      Y[.wki][.wki]
      (.var .vz)


-- set_option pp.explicit true
open Erased.Notation in
def pickStx : Tm Γ
    (.Pi
      (.El X)
      (.El
        (Tm.app (Γ := Γ; .El X) (A := .Sum .Unit .Unit) (B := .U)
          chooseStx[.wki]
          (.left .unit)
        )
      )
    )
  := Tm.lam <|
      (Tm.var .vz).conv <| by
        -- Note that most of these are `dsimp` (i.e. only `d`efinitional equalities).
        -- * So the proof essentially is only: `TyConv.El (TmConv.beta_redRight TmConv.elimSum_left)`
        dsimp [Ty.El_subst] -- compute subst
        apply TyConv.El -- congruence El
        dsimp [chooseStx]
        dsimp [Tm.lam_subst] -- compute subst
        rw [Tm.elimSum_subst] -- compute subst (also definitional, but dsimp breaks here for some reason)
        apply TmConv.beta_redRight'
        case a.c => aesop -- just a small technical/trivial proof
        dsimp only [Tm.conv_subst, Tm.conv_collapse] -- compute subst `(Tm.conv c t)[σ] = Tm.conv c[σ] t[σ]`
        rw [Tm.elimSum_subst] -- compute subst again
        dsimp only [Tm.conv_subst, Tm.conv_collapse] -- compute subst `(Tm.conv c t)[σ] = Tm.conv c[σ] t[σ]`
        -- We have `... (Tm.var Var.vz)[Subst.lift Subst.wki][Subst.apply (Tm.left Tm.unit)]`,
        -- which we compute away to just `.left .unit`.

        -- At this point, I am sure I could prove sufficient "boring" helpers to compute around all the `Tm.conv`,
        -- but for now it is easier to continue on preterms.
        -- This *does not* defeat the purpose of having an intrinsically typed syntax, since we're in the conversion proof.
        dsimp [Tm.conv, TmConv, Ty.El, Con.ext, Ty.U, Tm.elimSum, Tm.left, Tm.unit, Ty.Unit, Ty.Pi, Tm.var, Var.vz,
          Subst.apply, Subst.wki, Subst.lift, Ty.subst, Tm.subst, Subst.id, Subst.cons
        ]
        sorry
        done
