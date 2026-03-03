import Lean
import Aesop
import Qq
import Syntax.Elim.Shapeless

set_option pp.fieldNotation.generalized false
set_option linter.unusedVariables false
set_option pp.proofs true

/-
  The `*.recBelow` eliminator allows us to write easier pattern matching,
  for example a match arm such as `| Tm.app (Tm.lam body) a => ...`.
  For natural numbers, `Nat.brecOn` corresponds on strong induction.
-/

def below_methods (M : MotivesL) : MethodsL := {
  ConM Γ     := Type
  TyM Γ A    := Type
  TmM Γ A t  := Type
  VarM Γ A v := Type
  TmM_conv Γ A B t c := rfl
  nilM                           := Unit
  extM Γ Γd A Ad                 := (Γd × M.ConM Γ) × (Ad × M.TyM Γ A)
  UM Γ Γd                        := (Γd × M.ConM Γ)
  PiM Γ Γd A Ad B Bd             := (Γd × M.ConM Γ) × (Ad × M.TyM Γ A)    × (Bd × M.TyM _ B)
  ElM Γ Γd t td                  := (Γd × M.ConM Γ) × (td × M.TmM Γ .U t)
  SumM Γ Γd A Ad B Bd := sorry
  vzM Γ Γd A Ad                  := (Γd × M.ConM Γ) × (Ad × M.TyM Γ A)
  vsM Γ Γd A Ad B Bd v vd        := (Γd × M.ConM Γ) × (Ad × M.TyM Γ A)    × (Bd × M.TyM Γ B   ) × (vd × M.VarM Γ A v)
  varM Γ Γd A Ad v vd            := (Γd × M.ConM Γ) × (Ad × M.TyM Γ A)    × (vd × M.VarM Γ A v)
  lamM Γ Γd A Ad B Bd body bodyd := (Γd × M.ConM Γ) × (Ad × M.TyM Γ A)    × (Bd × M.TyM _ B   ) × (bodyd × M.TmM _ B body)
  piM Γ Γd A Ad B Bd             := (Γd × M.ConM Γ) × (Ad × M.TmM Γ .U A) × (Bd × M.TmM _ .U B)
  appM Γ Γd A Ad B Bd f fd a ad  := (Γd × M.ConM Γ) × (Ad × M.TyM Γ A)    × (Bd × M.TyM _ B   ) × (fd × M.TmM Γ _ f) × (ad × M.TmM Γ _ a)
  UnitM := sorry
  unitM := sorry
}

unsafe def Con.below (M : MotivesL) (Γ : Con)                          : Type := Con.recL (below_methods M) Γ
unsafe def Ty.below (M : MotivesL) {Γ : Con} (X : Ty Γ)                : Type := Ty.recL (below_methods M) X
unsafe def Tm.below (M : MotivesL) {Γ : Con} {X : Ty Γ} (t : Tm Γ X)   : Type := Tm.recL (below_methods M) t
unsafe def Var.below (M : MotivesL) {Γ : Con} {X : Ty Γ} (v : Var Γ X) : Type := Var.recL (below_methods M) v

-- It should be possible to turn this into a defeq
unsafe def Con.below.nil_iota : Con.below M .nil = Unit
  := by rw [Con.below, Con.nil_iota]; rfl

-- It should be possible to turn this into a defeq
unsafe def Con.below.ext_iota : Con.below M (.ext Γ A) = ((Con.below M Γ × M.ConM Γ) × (Ty.below M A × M.TyM Γ A))
  := by rw [Con.below, Con.ext_iota]; rfl

unsafe structure MotivesL.Below (M : MotivesL) where
  ConB : (Γ' : Con)     -> Con.below M Γ' -> M.ConM Γ'
  TyB  : (X' : Ty Γ)    -> Ty.below M X'  -> M.TyM Γ X'
  TmB  : (t' : Tm Γ A)  -> Tm.below M t'  -> M.TmM Γ A t'
  VarB : (v' : Var Γ A) -> Var.below M v' -> M.VarM Γ A v'


set_option diagnostics true in
unsafe def recLB_methods (M : MotivesL) (below : M.Below) : MethodsL := {
  ConM Γ     := Con.below M Γ × M.ConM Γ
  TyM Γ A    := Ty.below M A × M.TyM Γ A
  TmM Γ A t  := Tm.below M t × M.TmM Γ A t
  VarM Γ A v := Var.below M v × M.VarM Γ A v
  TmM_conv Γ A B t c := by sorry
  nilM  := ⟨Con.below.nil_iota ▸ (), below.ConB .nil (Con.below.nil_iota ▸ ())⟩ -- requires `Con.below.nil_iota ▸`. Although, this should be a cast by rfl, which should compute away.
  extM Γ Γd A Ad  :=
    let tmp : ((Con.below M Γ × M.ConM Γ) × (Ty.below M A × M.TyM Γ A)) := ⟨Γd, Ad⟩
    ⟨Con.below.ext_iota ▸ tmp, below.ConB (.ext Γ A) (Con.below.ext_iota ▸ tmp)⟩ -- * works! (but need cast...)
  UM Γ Γd  := sorry
  PiM Γ Γd A Ad B Bd  := sorry -- impl
  ElM Γ Γd t td  := sorry
  SumM Γ Γd A Ad B Bd := sorry
  vzM Γ Γd A Ad  := sorry
  vsM Γ Γd A Ad B Bd v vd  := sorry
  varM Γ Γd A Ad v vd  := sorry
  lamM Γ Γd A Ad B Bd body bodyd  := sorry
  piM Γ Γd A Ad B Bd  := sorry
  appM _ _ _ _ _ _ _ _ _ _  := sorry
  UnitM := sorry
  unitM := sorry
}

unsafe def Con.recLB (M : MotivesL) (Γ : Con) (below : M.Below) : M.ConM Γ
  := Con.recL (recLB_methods M below) Γ |>.2

unsafe def Ty.recLB (M : MotivesL) {Γ : Con} (A : Ty Γ) (below : M.Below) : M.TyM Γ A
  := Ty.recL (recLB_methods M below) A |>.2

unsafe def Tm.recLB (M : MotivesL) {Γ : Con} {A : Ty Γ} (t : Tm Γ A) (below : M.Below) : M.TmM Γ A t
  := Tm.recL (recLB_methods M below) t |>.2
