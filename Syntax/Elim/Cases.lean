import Aesop
import Qq
import Lean
import Syntax.Erased
import Syntax.Wellformed
import Syntax.AllTogether

set_option pp.fieldNotation.generalized false
set_option pp.proofs true

@[elab_as_elim]
def Con.cases {ConD : Con -> Sort u}
  (nilD : ConD .nil)
  (extD : (Γ : Con) -> (A : Ty Γ) -> ConD (.ext Γ A))
  : (Γ : Con) -> ConD Γ
  | ⟨0, .nil, _⟩ => nilD
  | ⟨n+1, .ext Γ A, w⟩ => extD ⟨n, Γ, w.ext_Γw⟩ ⟨A, w.ext_Aw⟩

@[simp] def Con.cases_nil : @Con.cases conD nilD extD .nil = nilD := rfl
@[simp] def Con.cases_ext : @Con.cases conD nilD extD (.ext Γ A) = extD Γ A := rfl

@[elab_as_elim]
def Ty.cases {Γ : Con} {TyD : {Γ : Con} -> Ty Γ -> Sort u}
  (UD : {Γ : Con} -> @TyD Γ .U)
  (PiD : {Γ : Con} -> (A : Ty Γ) -> (B : Ty (.ext Γ A)) -> @TyD Γ (.Pi A B))
  (ElD : {Γ : Con} -> (t : Tm Γ .U) -> @TyD Γ (.El t))
  (SumD : {Γ : Con} -> (A B : Ty Γ) -> @TyD Γ (.Sum A B))
  (UnitD : {Γ : Con} -> @TyD Γ .Unit)
  : (A : Ty Γ) -> TyD A
  | ⟨.U, _⟩ => UD
  | ⟨.Pi A B, w⟩ => PiD ⟨A, w.Pi_Aw⟩ ⟨B, w.Pi_Bw⟩
  | ⟨.El t, w⟩ => ElD ⟨t, w.El_tw⟩
  | ⟨.Sum A B, w⟩ => SumD ⟨A, sorry⟩ ⟨B, sorry⟩
  | ⟨.Unit, w⟩ => UnitD

@[elab_as_elim]
def Tm.cases {TmD : (Γ : Con) -> (X : Ty Γ) -> Tm Γ X -> Sort u}
  (TmDc : {Γ : Con} -> {A₁ A₂ : Ty Γ} -> (Ac : TyConv A₂ A₁) -> {t : Tm Γ A₂} -> TmD Γ A₁ (t.conv Ac) -> TmD Γ A₂ t)
  (varD : {Γ : Con} -> {A : Ty Γ} -> (v : Var Γ A) -> TmD Γ A (.var v))
  (appD : {Γ : Con} -> {A : Ty Γ} -> {B : Ty (Γ.ext A)} -> (f : Tm Γ (.Pi A B)) -> (a : Tm Γ A) -> TmD Γ (B.subst (.apply a)) (.app f a))
  (lamD : {Γ : Con} -> {A : Ty Γ} -> {B : Ty (Γ.ext A)} -> (body : Tm (Γ.ext A) B) -> TmD Γ (.Pi A B) (@Tm.lam Γ A B body))
  (piD  : {Γ : Con} -> (A : Tm Γ .U) -> (B : Tm (Γ.ext (.El A)) .U) -> TmD Γ .U (@Tm.pi Γ A B))
  {Γ : Con} {X : Ty Γ} (t : Tm Γ X) : TmD Γ X t
  := by
    let ⟨γ, Γe, Γw⟩ := Γ
    let ⟨Xe, Xw⟩ := X
    let ⟨te, tw⟩ := t
    dsimp at Xe Xw te tw
    clear t X
    match te with
    | .var ve =>
      let vw : VarW Γe Xe ve := sorry
      let v : Var ⟨γ, Γe, Γw⟩ ⟨Xe, Xw⟩ := ⟨ve, vw⟩
      exact varD v
    | .lam Ae Be bodye =>
      -- We can *not* pattern match on Xe, because there are infinitely many (think `.El "f ..."`). We only care that Xe is welltyped. And that `TyConv X (.Pi A B)`
      have ⟨Aw, Bw, bodyw⟩ := TmW.lam_wf tw
      have Xc : TyWConv Γe Xe (.Pi Ae Be) := TmW.lam_inv tw
      let Γ : Con := ⟨γ, Γe, Γw⟩
      let X : Ty Γ := ⟨Xe, Xw⟩
      let A : Ty Γ := ⟨Ae, Aw⟩
      let B : Ty (.ext Γ A) := ⟨Be, Bw⟩
      let body : Tm (.ext Γ A) B := ⟨bodye, bodyw⟩
      have Xc : TyConv X (.Pi A B) := Xc
      -- actually do the work:
      let ret : TmD Γ (.Pi A B) (@Tm.lam Γ A B body) := @lamD Γ A B body
      -- finally, repackage, using `TmDc`
      exact TmDc Xc ret
    | .app Ae Be fe ae =>
      have ⟨Aw, Bw, fw, aw⟩ := TmW.app_wf tw
      have Xc : TyWConv Γe Xe (Be.subst (.cons .id ae)) := TmW.app_inv tw
      let Γ : Con := ⟨γ, Γe, Γw⟩
      let X : Ty Γ := ⟨Xe, Xw⟩
      let A : Ty Γ := ⟨Ae, Aw⟩
      let B : Ty (.ext Γ A) := ⟨Be, Bw⟩
      let f : Tm Γ (.Pi A B) := ⟨fe, fw⟩
      let a : Tm Γ A := ⟨ae, aw⟩
      let ret := @appD Γ A B f a
      have Xc : @TyConv Γ X (B.subst (.apply a)) := Xc
      exact TmDc Xc ret
    | .pi Ae Be =>
      have ⟨Aw, Bw⟩ := TmW.pi_wf tw
      have Xc : TyWConv Γe Xe .U := TmW.pi_inv tw
      let Γ : Con := ⟨γ, Γe, Γw⟩
      let X : Ty Γ := ⟨Xe, Xw⟩
      let A : Tm Γ .U := ⟨Ae, Aw⟩
      let B : Tm (.ext Γ (.El A)) .U := ⟨Be, Bw⟩
      let ret := piD A B
      have Xc : @TyConv Γ X .U := Xc
      exact TmDc Xc ret
    | .left .. => sorry
    | .right .. => sorry
    | .elimSum .. => sorry
    | .unit => sorry
