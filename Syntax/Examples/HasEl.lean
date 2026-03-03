import Lean
import Aesop
import Qq
import Syntax.Elim.Shapeless

set_option pp.fieldNotation.generalized false
set_option linter.unusedVariables false
set_option pp.proofs true


inductive HasEl : (Γ : Con) -> Ty Γ -> Prop
| El : HasEl Γ (.El t)
| Pi_dom {Γ A B} : HasEl Γ A -> HasEl Γ (.Pi A B)
| Pi_cod {Γ A B} : HasEl (Γ.ext A) B -> HasEl Γ (.Pi A B)

theorem HasEl.Pi_aux : (h : HasEl Γ (.Pi A B)) -> ((∃d, h = HasEl.Pi_dom d) ∨ (∃c, h = HasEl.Pi_cod c)) := by
  intro h
  cases Γ
  cases A
  cases B
  rw [Ty.Pi] at h
  cases h
  dsimp at *
  case mk.mk.mk.Pi_dom h => simp_all only [Subtype.coe_eta, exists_const, exists_prop, and_true, true_or]
  case mk.mk.mk.Pi_cod h =>
    rename_i snd A B a property h_1
    simp_all only [Subtype.coe_eta, exists_prop, and_true]
    simp_all only [Subtype.coe_eta]
    simp_all only
    obtain ⟨val, property⟩ := snd
    simp_all only
    apply Or.inr
    exact a

open Notation in
def HasEl.Pi_aux2 {Γ: Con} {A : Ty Γ} {B : Ty (Γ.ext A)} {M : (Γ : Con) -> Ty Γ -> Sort u}
  : M Γ A -> M (Γ; A) B -> M Γ (.Pi A B)
  := by
    intro ma mb
    let ⟨γ, Γe, Γw⟩ := Γ
    let ⟨Ae, Aw⟩ := A
    let ⟨Be, Bw⟩ := B
    unfold Ty.Pi Con.ext at *
    dsimp
    dsimp at Ae Aw Be Bw ma mb
    sorry
    done

/-- Checks whether the type contains any `Ty.El` ctors. -/
unsafe def hasEl_disp : MethodsL := {
  ConM _ := Unit,
  TyM Γ A := Decidable (HasEl Γ A),
  TmM Γ A t := Unit,
  VarM Γ A t := Unit,
  TmM_conv _ _ _ _  c := rfl,
  nilM := ()
  extM _ _ _ _ := ()
  UM Γ Γd := .isFalse (fun prf => nomatch prf)
  UnitM _ _ := .isFalse (fun prf => nomatch prf)
  PiM Γ Γd A A_hasEl B B_hasEl :=
    match A_hasEl, B_hasEl with
    | .isTrue prfA                , _             => .isTrue (HasEl.Pi_dom prfA)
    | _                           , .isTrue prfB  => .isTrue (HasEl.Pi_cod prfB)
    | .isFalse (prfA : ¬HasEl Γ A), .isFalse prfB => .isFalse fun (h : HasEl Γ (Ty.Pi A B)) => by -- `⊢ False`
      /-
        Ideally, we want to do this:
          match h with -- ! But Lean isn't smart enough here, because `Ty.Pi` is not a ctor.
          | .Pi_dom (p : HasEl Γ A) => prfA p
          | .Pi_cod (p : HasEl (Γ; A) B) => prfB p
        So instead, we use a helper:
      -/
      match HasEl.Pi_aux h with
      | .inl ⟨(d : HasEl Γ A), (_ : h = HasEl.Pi_dom d)⟩ =>
        subst h
        exact prfA d
      | .inr ⟨(c : HasEl (Con.ext Γ A) B), h'⟩ =>
        subst h
        exact prfB c
  ElM Γ Γd t td := .isTrue .El
  SumM Γ Γd A Ad B Bd :=
    match Ad, Bd with
    | .isTrue prfA , _             => .isTrue sorry
    | _            , .isTrue prfB  => .isTrue sorry
    | .isFalse prfA, .isFalse prfB => .isFalse fun h => sorry
  vzM Γ Γd A Ad := ()
  vsM Γ Γd A Ad B Bd v vd := ()
  varM Γ Γd A Ad v vd := ()
  lamM Γ Γd A Ad B Bd body bodyd := ()
  piM Γ Γd A Ad B Bd := ()
  appM _ _ _ _ _ _ _ _ _ _ := ()
  unitM _ _ := ()
}

unsafe def hasEl (A : Ty Γ) : Decidable (HasEl Γ A) := Ty.recL hasEl_disp A

def ex0 : Ty .nil := .U
#reduce (types := true) hasEl ex0 -- isFalse

def ex1 : Ty .nil := .Pi .U .U
#reduce (types := true) hasEl ex1 -- isFalse

-- def ex2 : Ty .nil := Ty((X : Type) -> (x : X) -> Type)
def ex2 : Ty .nil := .Pi .U (.Pi (.El (.var .vz)) .U)
#reduce hasEl ex2 -- `.isTrue (HasEl.Pi_cod (HasEl.Pi_dom HasEl.El))`

def ex3 : Ty (Con.nil |>.ext .U |>.ext (.El (.var .vz))) := .Pi .U .U
#reduce hasEl ex3 -- isFalse
