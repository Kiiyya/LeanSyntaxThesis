import Aesop
import Qq
import Lean
import Syntax.Erased

set_option linter.unusedVariables false
set_option pp.fieldNotation.generalized false
open Erased.Notation ThinE VarE

/-
  # Wellformed
-/

mutual
  @[aesop 30%]
  inductive ConW : ConE γ -> Prop
  | nil : ConW .nil
  | ext : (Γw : ConW Γ) -> (Aw : TyW Γ A) -> ConW (.ext Γ A)

  @[aesop 10%]
  inductive TyW : ConE γ -> TyE γ -> Prop
  | U : ConW Γ -> TyW Γ .U
  | El : ConW Γ -> TmW Γ .U t -> TyW Γ (.El t)
  | Pi : ConW Γ -> TyW Γ A -> TyW (.ext Γ A) B -> TyW Γ (.Pi A B)
  | Sum : ConW Γ -> TyW Γ A -> TyW Γ B -> TyW Γ (.Sum A B)
  | Unit : ConW Γ -> TyW Γ .Unit

  @[aesop 10%]
  inductive VarW : ConE γ -> TyE γ -> VarE γ -> Prop
  /- `vz {Γ} {A : Ty Γ} : Var (Γ, A) A[wki]` -/
  | vz : (Γw : ConW Γ) -> (Aw : TyW Γ A) -> VarW (.ext Γ A) (A.ren .wki) .vz
  /- `vs {Γ} {A : Ty Γ} {B : Ty Γ} : Var Γ A -> Var (Γ, B) A[wki]` -/
  | vs {Γ A B v} : (Γw : ConW Γ) -> (Aw : TyW Γ A) -> (Bw : TyW Γ B) -> (vw : VarW Γ A v)
    -> VarW (.ext Γ B) (A.ren .wki) (.vs v)

  @[aesop 10%]
  inductive TmW : ConE γ -> TyE γ -> TmE γ -> Prop
  /-- `var {Γ} {A : Ty Γ} : Var Γ A -> Tm Γ A` -/
  | var : ConW Γ -> TyW Γ A -> VarW Γ A v -> TmW Γ A (.var v)
  /- `app {Γ : Con} {A : Ty Γ} {B : Ty (Γ; A)} : (f : Tm Γ (Pi A B)) -> (a : Tm Γ A) -> Tm Γ B[⟨id, a⟩]` -/
  | app : ConW Γ -> TyW Γ A -> TyW (.ext Γ A) B ->
    TmW Γ (.Pi A B) f ->
    TmW Γ A a ->
    TmW Γ (B.subst (.cons .id a)) (.app A B f a)
  /- `lam : {Γ} {A : Ty Γ} {B : Ty (Γ; A)} : (body : Tm (Γ; A) B) -> Tm Γ (Pi A B)` -/
  | lam : ConW Γ -> TyW Γ A -> TyW (.ext Γ A) B -> -- Γ, A, B
          TmW (.ext Γ A) B body -> -- body
          TmW Γ (.Pi A B) (.lam A B body)
  /-- `Tm.pi {Γ} : (A : Tm Γ .U) -> (B : Tm (Γ; A) .U) -> Tm Γ .U` -/
  | pi : ConW Γ -> TmW Γ .U A -> TmW (.ext Γ (.El A)) .U B -> TmW Γ .U (.pi A B)
  | conv : ConW Γ -> ConW Γ' -> TyW Γ A -> TyW Γ' A' -> (Γc : ConWConv Γ Γ') -> (Ac : TyWConv Γ A A') -> (tw : TmW Γ A t) -> TmW Γ' A' t
  | left : ConW Γ -> TyW Γ A -> TyW Γ B -> TmW Γ A a -> TmW Γ (.Sum A B) (.left a)
  | right : ConW Γ -> TyW Γ A -> TyW Γ B -> TmW Γ B b -> TmW Γ (.Sum A B) (.right b)
  | elimSum : ConW Γ -> TyW Γ A -> TyW Γ B ->
    TyW (.ext Γ (.Sum A B)) Mot ->
    TmW (.ext Γ A) (Mot.subst (.cons .wki (.left  (.var .vz)))) leftM  -> -- `Γ; A ⊢ leftM : Mot[.left #0]`
    TmW (.ext Γ B) (Mot.subst (.cons .wki (.right (.var .vz)))) rightM -> -- `Γ; B ⊢ rightM : Mot[.right #0]`
    TmW Γ (.Sum A B) t ->
    TmW Γ (Mot.subst (.cons .id t)) (.elimSum A B Mot leftM rightM t)
  | unit : ConW Γ -> TmW Γ .Unit .unit

  @[aesop 10%]
  inductive ThinW : ConE γ -> ConE δ -> ThinE γ δ -> Prop
  | nil : ConW Γ -> ThinW Γ .nil .nil
  | wk {Γ : ConE γ} {Δ : ConE δ} {W σ} : ConW Γ -> ConW Δ -> TyW Γ W ->
      ThinW Γ Δ σ ->
      ThinW (Γ.ext W) Δ (.wk σ)
  | lift {Γ : ConE γ} {Δ : ConE δ} {W σ} : ConW Γ -> ConW Δ -> TyW Δ W ->
      ThinW Γ Δ σ ->
      ThinW (Γ.ext (W.ren σ)) (Δ.ext W) (.lift σ)

  @[aesop 10%]
  inductive SubstW : ConE γ -> ConE δ -> SubstE γ δ -> Prop
  | nil : ConW Γ -> SubstW Γ .nil .nil
  /- `Subst.cons {Γ} {Δ} {A : Ty Δ} : (σ : Susbt Γ Δ) -> (t : Tm Γ A[σ]) -> Subst Γ (Δ; A)` -/
  | cons : ConW Γ -> ConW Δ -> TyW Δ A ->
      SubstW Γ Δ σ ->
      TmW Γ (A.subst σ) t ->
      SubstW Γ (.ext Δ A) (.cons σ t)

  @[aesop 10%]
  inductive ConWConv: ConE γ -> ConE δ -> Prop
  | refl : ConW Γ -> ConWConv Γ Γ
  | symm : ConWConv Γ Γ' -> ConWConv Γ' Γ
  | trans : ConWConv Γ₁ Γ₂ -> ConWConv Γ₂ Γ₃ -> ConWConv Γ₁ Γ₃
  | nil : ConWConv .nil .nil
  | ext : ConWConv Γ Γ' -> TyWConv Γ A A' -> ConWConv (.ext Γ A) (.ext Γ' A')

  @[aesop 10%]
  inductive TyWConv : (Γ : ConE γ) -> TyE γ -> TyE γ -> Prop
  | refl : ConW Γ -> TyW Γ A -> TyWConv Γ A A
  | symm : TyWConv Γ A B -> TyWConv Γ B A
  | trans (Γw : ConW Γ) (Xw : TyW Γ X) (Yw : TyW Γ Y) (Zw : TyW Γ Z) (c1 : TyWConv Γ X Y) (c2 : TyWConv Γ Y Z) : TyWConv Γ X Z
  | U : ConW Γ -> TyWConv Γ .U .U
  | Pi : ConW Γ -> TyW Γ A -> TyW Γ A' -> TyW (Γ.ext A) B -> TyW (Γ.ext A') B' -> TyWConv Γ A A' ->
    TyWConv (Γ.ext A) B B' -> TyWConv Γ (.Pi A B) (.Pi A' B')
  | El : ConW Γ -> TmW Γ .U t -> TmW Γ .U t' -> TmWConv Γ .U t t' -> TyWConv Γ (.El t) (.El t')

  @[aesop 10%]
  inductive TmWConv : (Γ : ConE γ) -> (A : TyE γ) -> TmE γ -> TmE γ -> Prop
  | refl  : ConW Γ -> TyW Γ A -> TmW Γ A a -> TmWConv Γ A a a
  | symm  : TmWConv Γ A a₁ a₂ -> TmWConv Γ A a₂ a₁
  | trans : TmWConv Γ A a₁ a₂ -> TmWConv Γ A a₂ a₃ -> TmWConv Γ A a₁ a₃
  | app   : ConW Γ -> TyW Γ A -> TyW (Γ; A) B -> TmW Γ (.Pi A B) f -> TmW Γ (.Pi A B) f' -> TmW Γ A a -> TmW Γ A a' ->
      TmWConv Γ (.Pi A B) f f' -> TmWConv Γ A a a' -> TmWConv Γ (B.subst (.cons .id a)) (.app A B f a) (.app A B f' a')
  | lam   : ConW Γ -> TyW Γ A -> TyW (Γ;A) B -> TmW (Γ; A) B body -> TmW (Γ; A) B body' ->
      TmWConv (Γ; A) B body body' -> TmWConv Γ (.Pi A B) (.lam A B body) (.lam A B body')
  | beta  : ConW Γ -> TyW Γ A -> TyW (Γ; A) B -> TmW Γ A a -> TmW (Γ.ext A) B body ->
      TmWConv Γ (B.subst (.cons .id a)) (.app A B (.lam A B body) a) (body.subst (.cons .id a))
  | eta   : ConW Γ -> TyW Γ A -> TyW (Γ.ext A) B -> TmW Γ (.Pi A B) f ->
      TmWConv Γ (.Pi A B) (.lam A B (.app A[.wki] B[.wki] f[.wki] (.var .vz))) f
    -- equivalent repr of eta: TmWConv (f #0) (g #0) -> TmWConv f g
  | conv (Γc : ConWConv Γ₁ Γ₂) (Xc : TyWConv Γ₁ X₁ X₂) (tc : TmWConv Γ₁ X₁ t₁ t₂) : TmWConv Γ₂ X₂ t₁ t₂

  /-- Iota reduction rule for sum types. Note that the `a` here is a term in context Γ, not a variable from the context.
    `Γ ⊢ elimSum Mot leftM rightM (.left a) ≡ leftM a : Mot[.left a]` -/
  | sum_left : ConW Γ -> TyW Γ A -> TyW Γ B ->
    TyW (.ext Γ (.Sum A B)) Mot -> -- `Γ; A+B ⊢ Mot`
    TmW (.ext Γ A) (Mot.subst (.cons .wki (.left  (.var .vz)))) leftM  -> -- `Γ; A ⊢ leftM : Mot[.left #0]`
    TmW (.ext Γ B) (Mot.subst (.cons .wki (.right (.var .vz)))) rightM -> -- `Γ; B ⊢ rightM : Mot[.right #0]`
    TmW Γ A a -> -- `Γ ⊢ a : A`
    TmWConv Γ
      (Mot.subst <| .cons .id (.left a)) -- `Γ ⊢ Mot[.left a]`
      (.elimSum A B Mot leftM rightM (.left a)) -- `Γ ⊢ elimSum Mot liftM rightM (.left a)`
      (leftM.subst (.cons .id a)) -- `Γ ⊢ liftM[a]`

  | sum_right : ConW Γ -> TyW Γ A -> TyW Γ B ->
    TyW (.ext Γ (.Sum A B)) Mot -> -- `Γ; A+B ⊢ Mot`
    TmW (.ext Γ A) (Mot.subst (.cons .wki (.left  (.var .vz)))) leftM  -> -- `Γ; A ⊢ leftM : Mot[.left #0]`
    TmW (.ext Γ B) (Mot.subst (.cons .wki (.right (.var .vz)))) rightM -> -- `Γ; B ⊢ rightM : Mot[.right #0]`
    TmW Γ B b -> -- `Γ ⊢ a : A`
    TmWConv Γ
      (Mot.subst <| .cons .id (.right b)) -- `Γ ⊢ Mot[.left a]`
      (.elimSum A B Mot leftM rightM (.right b)) -- `Γ ⊢ elimSum Mot liftM rightM (.left a)`
      (rightM.subst (.cons .id b)) -- `Γ ⊢ liftM[a]`
end

namespace Wellformed.Notation
  scoped notation:50 (name := stxConW) Γ " ctx" => ConW Γ
  scoped notation:50 (name := stxTyW)     Γ " ⊢ " A => TyW Γ A
  scoped notation:50 (name := stxTmW)     Γ " ⊢ " t " : " A => TmW Γ A t
  scoped notation:50 (name := stxTyWConv) Γ " ⊢ " A " ≅ " B => TyWConv Γ A B
  scoped notation:50 (name := stxTmWConv) Γ " ⊢ " x " ≅ " y " : " A => TmWConv Γ A x y
end Wellformed.Notation
open Wellformed.Notation


@[aesop safe forward] theorem ConWConv.same_len {Γ : ConE γ} {Δ : ConE δ} (c : ConWConv Γ Δ) : γ = δ :=
  match c with
  | .refl Γw => rfl
  | .symm c =>
    let ih := same_len c
    by omega
  | .trans c1 c2 =>
    let ih1 := same_len c1
    let ih2 := same_len c2
    by omega
  | .nil => rfl
  | .ext Γw Aw => rfl

section WfHelpers

-- attribute [aesop unsafe 50% apply] TmW.conv

@[aesop unsafe 50% apply]
-- @[aesop [50% apply, norm forward (immediate := [Γc, Aw])]]
theorem TyW.conv' (Γw : ConW Γ) (Δw : ConW Δ) (Γc : ConWConv Γ Δ) : (Aw : TyW Γ A) -> TyW Δ A := by
  match A with
  | .U => exact fun (.U Γw) => .U Δw
  | .El t => exact fun (.El Γw tw) => .El Δw (TmW.conv Γw Δw (.U Γw) (.U Δw) Γc (.refl Γw (.U Γw)) tw)
  | .Pi A B => exact fun (.Pi Γw Aw Bw) => .Pi Δw (TyW.conv' Γw Δw Γc Aw) (TyW.conv' (.ext Γw Aw) (.ext Δw (TyW.conv' Γw Δw Γc Aw)) (.ext Γc (.refl Γw Aw)) Bw)
  | .Sum A B => exact fun (.Sum Γw Aw Bw) => .Sum Δw (TyW.conv' Γw Δw Γc Aw) (TyW.conv' Γw Δw Γc Bw)
  | .Unit => exact fun (.Unit Γw) => .Unit Δw

mutual
  @[aesop 11%] def TyWConv.w_left : TyWConv Γ X Y -> TyW Γ X
  | .refl Γw Xw => Xw
  | .symm c => c.w_right
  | .trans Γw Xw Yw Zw c₁ c₂ => Xw
  | .U Γw => .U Γw
  | .Pi Γw A₁w A₂w B₁w B₂w Ac Bc => .Pi Γw A₁w B₁w
  | .El Γw t₁w t₂w tc => .El Γw t₁w
  termination_by structural c => c

  @[aesop 11%] def TyWConv.w_right : TyWConv Γ X Y -> TyW Γ Y
  | .refl Γw Xw => Xw
  | .symm c => c.w_left
  | .trans Γw Xw Yw Zw c₁ c₂ => Zw
  | .U Γw => .U Γw
  | .Pi Γw A₁w A₂w B₁w B₂w Ac Bc => .Pi Γw A₂w B₂w
  | .El Γw t₁w t₂w tc => .El Γw t₂w
  termination_by structural c => c
end


@[aesop 10%] def TyWConv.w_con : TyWConv Γ X Y -> ConW Γ
| .refl Γw Xw => Γw
| .symm c => c.w_con
| .trans Γw Xw Yw Zw c₁ c₂ => Γw
| .U Γw => Γw
| .Pi Γw A₁w A₂w B₁w B₂w Ac Bc => Γw
| .El Γw t₁w t₂w tc => Γw
termination_by structural c => c

mutual
  @[aesop 10%] def ConWConv.w_left : ConWConv Γ₁ Γ₂ -> ConW Γ₁
  | .refl Γw => Γw
  | .symm c => c.w_right
  | .trans c1 c2 => c1.w_left
  | .nil => .nil
  | .ext Γc Ac => .ext Γc.w_left Ac.w_left
  termination_by structural c => c

  @[aesop 10%] def ConWConv.w_right : ConWConv Γ₁ Γ₂ -> ConW Γ₂
  | .refl Γw => Γw
  | .symm c => c.w_left
  | .trans c1 c2 => c2.w_right
  | .nil => .nil
  | .ext Γc Ac => .ext Γc.w_right (TyW.conv' Γc.w_left Γc.w_right Γc Ac.w_right)
  termination_by structural c => c
end

@[aesop 10%] def TyW.w_con : TyW Γ A -> ConW Γ
| .U Γw => Γw
| .El Γw _ => Γw
| .Pi Γw _ _ => Γw
| .Sum Γw .. => Γw
| .Unit Γw => Γw
@[aesop 1%] def ConW.ext_Γw : ConW (.ext Γ A) -> ConW Γ | .ext Γw Aw => Γw
@[aesop 1%] def ConW.ext_Aw : ConW (.ext Γ A) -> TyW Γ A | .ext Γw Aw => Aw
@[aesop 1%] def TyW.El_tw : TyW Γ (.El t) -> TmW Γ .U t | .El Γw tw => tw
@[aesop 1%] def TyW.Pi_Aw : TyW Γ (.Pi A B) -> TyW Γ A | .Pi Γw Aw Bw => Aw
@[aesop 1%] def TyW.Pi_Bw : TyW Γ (.Pi A B) -> TyW (.ext Γ A) B | .Pi Γw Aw Bw => Bw
@[aesop 1%] def TyW.Sum_wf : TyW Γ (.Sum A B) -> TyW Γ A ∧ TyW Γ B | .Sum Γw Aw Bw => ⟨Aw, Bw⟩
def TyW.Sum_w_Left : TyW Γ (.Sum A B) -> TyW Γ A | .Sum Γw Aw Bw => Aw
def TyW.Sum_w_Right : TyW Γ (.Sum A B) -> TyW Γ B | .Sum Γw Aw Bw => Bw

end WfHelpers


@[aesop unsafe [50% apply]]
-- @[aesop [50% apply, norm forward (immediate := [Γc, Aw])]]
theorem TyW.conv (Γc : ConWConv Γ Δ) : (Aw : TyW Γ A) -> TyW Δ A := by -- version of `TyW.conv'` but with fewer requirements
  match A with
  | .U => exact fun (.U Γw) => .U Γc.w_right
  | .El t => exact fun (.El Γw tw) => .El Γc.w_right (TmW.conv Γw Γc.w_right (.U Γw) (.U Γc.w_right) Γc (.refl Γw (.U Γw)) tw)
  | .Pi A B => exact fun (.Pi Γw Aw Bw) => .Pi Γc.w_right (TyW.conv Γc Aw) (TyW.conv (.ext Γc (.refl Γw Aw)) Bw)
  | .Sum A B => exact fun (.Sum Γw Aw Bw) => .Sum Γc.w_right (TyW.conv Γc Aw) (TyW.conv Γc Bw)
  | .Unit => exact fun (.Unit Γw) => .Unit Γc.w_right

@[aesop 50%] theorem TmW.conv_easy (Γc : ConWConv Γ Γ') (Ac : TyWConv Γ A A') (tw : TmW Γ A t) : TmW Γ' A' t :=
  TmW.conv Γc.w_left Γc.w_right Ac.w_left (Ac.w_right.conv Γc) Γc Ac tw


@[aesop norm forward]
theorem TmW.lam_wf (w : TmW Γ X (.lam A B body)) : TyW Γ A ∧ TyW (Γ.ext A) B ∧ TmW (Γ.ext A) B body :=
  impl w rfl
where impl {γ} {Γ : ConE γ} {X LAM A B body} (w : TmW Γ X LAM) (h : LAM = (.lam A B body)) : TyW Γ A ∧ TyW (Γ.ext A) B ∧ TmW (Γ.ext A) B body :=
  match w with
  | TmW.lam Γw Aw Bw bodyw => by simp_all only [TmE.lam.injEq, and_self]
  | @TmW.conv .(γ) Γ' .(Γ) X' X (.lam A_ B_ body_) Γ'w Γw X'w Xw Γc Xc body'w => by
    let ⟨A_w, B_w, body_w⟩ := impl (LAM := TmE.lam A_ B_ body_) body'w rfl -- we can do this because body'w is smaller
    have hA : A = A_ := by simp_all only [TmE.lam.injEq]
    subst hA
    have hB : B = B_ := by simp_all only [TmE.lam.injEq, true_and]
    subst hB
    have hbody : body = body_ := by simp_all only [TmE.lam.injEq, true_and]
    subst hbody
    let Aw    := TyW.conv' Γ'w Γw Γc A_w
    let Bw    := TyW.conv' (Γ := Γ'.ext A) (Δ := Γ.ext A) (Γ'w.ext A_w) (Γw.ext Aw) (Γc.ext (.refl Γ'w A_w)) B_w
    let bodyw := TmW.conv_easy (Γc.ext (.refl Γ'w A_w)) (.refl (.ext Γ'w A_w) B_w) body_w
    exact ⟨Aw, Bw, bodyw⟩
  termination_by structural w


@[aesop norm forward]
theorem TmW.app_wf (w : TmW Γ X (.app A B f a)) : TyW Γ A ∧ TyW (Γ.ext A) B ∧ TmW Γ (.Pi A B) f ∧ TmW Γ A a :=
  impl w rfl
where impl {γ} {Γ : ConE γ} {X APP A B f a} (w : TmW Γ X APP) (h : APP = .app A B f a) : TyW Γ A ∧ TyW (Γ.ext A) B ∧ TmW Γ (.Pi A B) f ∧ TmW Γ A a :=
  match w with
  | TmW.app Γw Aw Bw fw aw => by simp_all only [TmE.app.injEq, and_self]
  | @TmW.conv .(γ) Γ' .(Γ) X' X (.app A_ B_ f_ a_) Γ'w Γw X'w Xw Γc Xc body'w => by
    let ⟨A_w, B_w, f_w, a_w⟩ := impl (APP := TmE.app A_ B_ f_ a_) body'w rfl -- we can do this because body'w is smaller
    have hA : A = A_ := by simp_all only [TmE.app.injEq]
    subst hA
    have hB : B = B_ := by simp_all only [TmE.app.injEq]
    subst hB
    have hf : f = f_ := by simp_all only [TmE.app.injEq]
    subst hf
    have ha : a = a_ := by simp_all only [TmE.app.injEq]
    subst ha
    let Aw : TyW Γ A := TyW.conv' Γ'w Γw Γc A_w
    let Bw : TyW (Γ.ext A) B := TyW.conv' (Γ := Γ'.ext A) (Δ := Γ.ext A) (Γ'w.ext A_w) (Γw.ext Aw) (Γc.ext (.refl Γ'w A_w)) B_w
    let fw : TmW Γ (.Pi A B) f := TmW.conv_easy Γc (.refl Γ'w (TyW.Pi Γ'w A_w B_w)) f_w
    let aw : TmW Γ A a := TmW.conv_easy Γc (TyWConv.refl Γ'w A_w) a_w
    exact ⟨Aw, Bw, fw, aw⟩
  termination_by structural w

#print axioms TmW.app_wf

@[aesop norm forward]
theorem TmW.pi_wf (w : TmW Γ X (.pi A B)) : TmW Γ .U A ∧ TmW (Γ.ext (.El A)) .U B :=
  impl w rfl
where impl {γ} {Γ : ConE γ} {X PI A B} (w : TmW Γ X PI) (h : PI = .pi A B) : TmW Γ .U A ∧ TmW (Γ.ext (.El A)) .U B :=
  match w with
  | TmW.pi Γw Aw Bw => by simp_all only [TmE.pi.injEq, and_self]
  | @TmW.conv .(γ) Γ' .(Γ) X' X (.pi A_ B_) Γ'w Γw X'w Xw Γc Xc body'w => by
    let ⟨A_w, B_w⟩ := impl (PI := TmE.pi A_ B_) body'w rfl -- we can do this because body'w is smaller
    have hA : A = A_ := by simp_all only [TmE.pi.injEq]
    subst hA
    have hB : B = B_ := by simp_all only [TmE.pi.injEq]
    subst hB
    let Aw : TmW Γ .U A := TmW.conv_easy Γc (.refl Γ'w (.U Γ'w)) A_w
    have ΓAc : ConWConv (Γ'; TyE.El A) (Γ; TyE.El A) := ConWConv.ext Γc (.refl Γ'w (.El Γ'w A_w))
    have Uc : TyWConv (Γ'; TyE.El A) TyE.U TyE.U := TyWConv.refl (.ext Γ'w (.El Γ'w A_w)) (.U (.ext Γ'w (.El Γ'w A_w)))
    let Bw : TmW (.ext Γ (.El A)) .U B := TmW.conv_easy ΓAc Uc B_w
    exact ⟨Aw, Bw⟩
  termination_by structural w


@[aesop safe forward] theorem TmW.lam_wf₁ (w : TmW Γ X (.lam A B body)) : TyW Γ A := TmW.lam_wf w |>.1
@[aesop safe forward] theorem TmW.lam_wf₂ (w : TmW Γ X (.lam A B body)) : TyW (Γ.ext A) B := TmW.lam_wf w |>.2.1
@[aesop safe forward] theorem TmW.lam_wf₃ (w : TmW Γ X (.lam A B body)) : TmW (Γ.ext A) B body := TmW.lam_wf w |>.2.2
@[aesop safe forward] theorem TmW.app_wf₁ (w : TmW Γ X (.app A B f a)) : TyW Γ A := TmW.app_wf w |>.1
@[aesop safe forward] theorem TmW.app_wf₂ (w : TmW Γ X (.app A B f a)) : TyW (Γ.ext A) B := TmW.app_wf w |>.2.1
@[aesop safe forward] theorem TmW.app_wf₃ (w : TmW Γ X (.app A B f a)) : TmW Γ (.Pi A B) f := TmW.app_wf w |>.2.2.1
@[aesop safe forward] theorem TmW.app_wf₄ (w : TmW Γ X (.app A B f a)) : TmW Γ A a := TmW.app_wf w |>.2.2.2
@[aesop safe forward] theorem TmW.pi_wf₁ (w : TmW Γ X (.pi A B)) : TmW Γ .U A := TmW.pi_wf w |>.1
@[aesop safe forward] theorem TmW.pi_wf₂ (w : TmW Γ X (.pi A B)) : TmW (Γ.ext (.El A)) .U B := TmW.pi_wf w |>.2


@[aesop 10%] theorem TyWConv.conv (Γc : ConWConv Γ₁ Γ₂) (Xc : TyWConv Γ₁ X₁ X₂) : TyWConv Γ₂ X₁ X₂ := by
  have Γ₁w : ConW Γ₁ := ConWConv.w_left Γc
  have Γ₂w : ConW Γ₂ := ConWConv.w_right Γc
  have X₁w : TyW Γ₁ X₁ := Xc.w_left
  have X₂w : TyW Γ₁ X₂ := Xc.w_right
  match Xc with
  | .refl Γ₁w X₁w => exact .refl Γ₂w (TyW.conv' Γ₁w Γ₂w Γc X₁w)
  | .symm Xc => exact .symm (TyWConv.conv Γc Xc)
  | .trans (Y := Y) _ _ Yw _ Xc1 Xc2 =>
    have ih1 := TyWConv.conv Γc Xc1
    have ih2 := TyWConv.conv Γc Xc2
    exact .trans Γ₂w ih1.w_left ih2.w_left (TyW.conv' Γ₁w Γ₂w Γc X₂w) ih1 ih2
  | .U .. => exact .U Γ₂w
  | .El (t := t) (t' := t') _ tw t'w tc => exact .El Γ₂w (tw.conv_easy Γc (.refl Γ₁w (.U Γ₁w))) (t'w.conv_easy Γc (.refl Γ₁w (.U Γ₁w))) (TmWConv.conv Γc (.refl Γ₁w (.U Γ₁w)) tc)
  | .Pi (A := A) (B := B) (A' := A') (B' := B') _ Aw A'w Bw B'w Ac Bc =>
    have ihA := TyWConv.conv Γc Ac
    have ihB_1 : Γ₂; A' ⊢ B ≅ B' := TyWConv.conv (Γc.ext Ac) Bc
    have ihB_2 : Γ₂; A ⊢ B ≅ B' := TyWConv.conv (ConWConv.ext Γc (.refl Γ₁w Aw)) Bc
    exact .Pi (B := B) (B' := B') Γ₂w ihA.w_left ihA.w_right ihB_2.w_left ihB_1.w_right ihA ihB_2
  done

mutual
  @[simp] def ConE.size : ConE γ -> Nat
  | .nil => 1
  | .ext Γ A => 1 + Γ.size + A.size

  @[simp] def TyE.size : TyE γ -> Nat
  | .U => 1
  | .Unit => 1
  | .El t => 1 + t.size
  | .Pi A B => 1 + A.size + B.size
  | .Sum A B => 1 + A.size + B.size

  @[simp] def TmE.size : TmE γ -> Nat
  | .var v => 1 -- ignore variable size!
  | .unit => 1
  | .left a => 1 + a.size
  | .right b => 1 + b.size
  | .lam A B b => 1 + A.size + B.size + b.size
  | .app A B f a => 1 + A.size + B.size + f.size + a.size
  | .pi A B => 1 + A.size + B.size
  | .elimSum A B M l r t => 1 + A.size + B.size + M.size + l.size + r.size + t.size
end


mutual
  @[simp] theorem TmE.ren_preserve_size : (t : TmE γ) -> t⌊σ⌋.size = t.size
  | .var v => rfl
  | .unit => rfl
  | .left a => by
    have ih := TmE.ren_preserve_size (σ := σ) a
    simp only [TmE.ren, TmE.size, *]
  | .right b => by
    have ih := TmE.ren_preserve_size (σ := σ) b
    simp only [TmE.ren, TmE.size, *]
  | .lam A B b => by
    have ihA := TyE.ren_preserve_size (σ := σ) A
    have ihB := TyE.ren_preserve_size (σ := σ.lift) B
    have ihb := TmE.ren_preserve_size (σ := σ.lift) b
    simp only [ TmE.ren, TmE.size, *]
  | .app A B f a => by
    have ihA := TyE.ren_preserve_size (σ := σ) A
    have ihB := TyE.ren_preserve_size (σ := σ.lift) B
    have ihf := TmE.ren_preserve_size (σ := σ) f
    have iha := TmE.ren_preserve_size (σ := σ) a
    simp only [TmE.ren, TmE.size, *]
  | .pi A B => by
    have ihA := TmE.ren_preserve_size (σ := σ) A
    have ihB := TmE.ren_preserve_size (σ := σ.lift) B
    simp only [TmE.ren, TmE.size, *]
  | .elimSum A B M l r t => by
    have ihA := TyE.ren_preserve_size (σ := σ) A
    have ihB := TyE.ren_preserve_size (σ := σ) B
    have ihM := TyE.ren_preserve_size (σ := σ.lift) M
    have ihl := TmE.ren_preserve_size (σ := σ.lift) l
    have ihr := TmE.ren_preserve_size (σ := σ.lift) r
    have iht := TmE.ren_preserve_size (σ := σ) t
    simp only [TmE.ren, TmE.size, *]

  @[simp] theorem TyE.ren_preserve_size : (W : TyE γ) -> W⌊σ⌋.size = W.size
  | .U => rfl
  | .Unit => rfl
  | .Pi A B => by
    have ihA := TyE.ren_preserve_size (σ := σ) A
    have ihB := TyE.ren_preserve_size (σ := σ.lift) B
    simp only [TyE.ren, TyE.size, ihA, ihB]
  | .Sum A B => by
    have ihA := TyE.ren_preserve_size (σ := σ) A
    have ihB := TyE.ren_preserve_size (σ := σ) B
    simp only [TyE.ren, TyE.size, ihA, ihB]
  | .El t => by
    have ih := TmE.ren_preserve_size (σ := σ) t
    simp only [TyE.ren, TyE.size, ih]
end

abbrev ThinE.amount_wk : ThinE γ δ -> Nat
| .nil => 0
| .lift σ => σ.amount_wk
| .wk σ => 1 + σ.amount_wk

@[aesop 10%] def ThinW.comp (Γw : @ConW γ Γ) (Θw : @ConW θ Θ) (Δw : @ConW δ Δ)
  (σ₁w : @ThinW θ δ Θ Δ σ₁)
  (σ₂w : @ThinW γ θ Γ Θ σ₂)
  : @ThinW γ δ Γ Δ (.comp σ₁ σ₂)
  := by
    match γ, Γ, Γw, θ, Θ, Θw, δ, Δ, Δw, σ₁, σ₁w, σ₂, σ₂w with
    | γ+1, .ext Γ A, .ext Γw Aw, θ  ,      Θ  ,      Θw   , δ  ,      Δ  ,      Δw    , σ₁                      , σ₁w, @ThinE.wk   .(γ) .(θ) σ₂, .wk _ _ _ σ₂w => -- .wk   (ThinE.comp σ₁ σ₂)
      rw [ThinE.comp]
      have ih := ThinW.comp Γw Θw Δw σ₁w σ₂w
      exact ThinW.wk Γw Δw Aw ih
    | γ  ,      Γ  ,      Γw   , 0  , .nil    , .nil      , 0  , .nil    , Δw         , .nil                    , σ₁w, .nil                    , .nil .. =>  -- nil
      rw [ThinE.comp]
      exact .nil Γw
    | γ+1, .ext Γ A, .ext Γw Aw, θ+1, .ext Θ B, .ext Θw Bw, 0  , .nil    , .nil       , .nil                    , σ₁w, @ThinE.lift .(γ) .(θ) σ₂, σ₂w =>  -- nil
      rw [ThinE.comp]
      exact .nil (Γw.ext Aw)
    | γ+1, .ext Γ A, .ext Γw Aw, θ+1, .ext Θ B, .ext Θw Bw, δ  ,      Δ  ,      Δw    , @ThinE.wk   .(θ) .(δ) σ₁, .wk _ _ _ σ₁w, @ThinE.lift .(γ) .(θ) σ₂, σ₂w =>  -- wk (comp 1 2)
      cases σ₂w
      rw [ThinE.comp]
      have ih : ThinW Γ Δ (σ₁ ∘ σ₂) := ThinW.comp Γw Θw Δw σ₁w ‹ThinW Γ Θ σ₂›
      exact .wk Γw Δw Aw ih
    | γ+1, .ext Γ A, .ext Γw Aw, θ+1, .ext Θ B, .ext Θw Bw, δ+1, .ext Δ C, .ext Δw Cw , @ThinE.lift .(θ) .(δ) σ₁, σ₁w, @ThinE.lift .(γ) .(θ) σ₂, σ₂w => -- lift (comp 1 2)
      cases σ₁w
      cases σ₂w
      rw [ThinE.comp]
      have ih : ThinW Γ Δ (σ₁ ∘ σ₂) := ThinW.comp Γw Θw Δw ‹ThinW Θ Δ σ₁› ‹ThinW Γ Θ σ₂›
      have h := ThinW.lift Γw Δw ‹Δ ⊢ C› ih
      rw [TyE.ren_comp] -- We can use our theorems on erased terms here :)
      exact h
    | γ  ,      Γ  ,      Γw   , 0  , .nil    , .nil      , δ+1  , Δ       , Δw         , σ1                    , σ₁w, .nil                    , .nil .. => nomatch σ1

#print axioms ThinW.comp


@[aesop 10%] def ThinW.id : {Γ : ConE γ} -> ConW Γ -> ThinW Γ Γ (ThinE.id _)
| .nil    , .nil       => .nil .nil
| .ext Γ A, .ext Γw Aw => by
  rw [ThinE.id]
  have h := ThinW.lift Γw Γw Aw (ThinW.id Γw)
  rw [TyE.ren_id] at h
  exact h

@[aesop 10%] def ThinW.wki : ConW Γ -> TyW Γ W -> ThinW (.ext Γ W) Γ ThinE.wki := by
  intro a_1 a_2
  simp_all only [ThinE.wki]
  apply ThinW.wk
  · simp_all only
  · simp_all only
  · simp_all only
  · apply ThinW.id
    simp_all only

@[aesop 50%] def TyWConv.thin {Γ:ConE γ} {Δ:ConE δ} {X Y : TyE δ}
  (Γw : ConW Γ) (σw : ThinW Γ Δ σ) (c : Δ ⊢ X ≅ Y) : Γ ⊢ X⌊σ⌋ ≅ Y⌊σ⌋
  :=
  match h : c with
  | @TyWConv.refl _ Δ A Δw Aw => sorry
  | @TyWConv.symm _ Δ X Y c => sorry
  | @TyWConv.trans _ Δ X Y Z Δw Xw Yw Zw c1 c2 => sorry
  | @TyWConv.U _ Δ Δw => by
    rw [TyE.ren]
    exact TyWConv.refl Γw (.U Γw)
  | @TyWConv.Pi _ Δ A A' B B' Δw Aw A'w Bw B'w Ac Bc =>
    have ihA  : Γ        ⊢ A⌊σ⌋       ≅ A'⌊σ⌋       := TyWConv.thin Γw σw Ac
    have Aσw  : Γ        ⊢ A⌊σ⌋                     := ihA.w_left
    have A'σw : Γ        ⊢ A'⌊σ⌋                    := ihA.w_right
    have ihB  : Γ; A⌊σ⌋  ⊢ B⌊.lift σ⌋ ≅ B'⌊.lift σ⌋ := TyWConv.thin (Γw.ext Aσw) (.lift Γw Δw Aw σw) Bc
    have Bσw  : Γ; A⌊σ⌋  ⊢ B⌊.lift σ⌋               := ihB.w_left
    have B'σw : Γ; A'⌊σ⌋ ⊢ B'⌊.lift σ⌋              := TyW.conv ((ConWConv.refl Γw).ext ihA) (ihB.w_right)
    by
      rw [TyE.ren, TyE.ren]
      exact @TyWConv.Pi _ Γ A⌊σ⌋ A'⌊σ⌋ B⌊.lift σ⌋ B'⌊.lift σ⌋ Γw Aσw A'σw Bσw B'σw ihA ihB
  | @TyWConv.El _ Δ t t' Δw tw t'w c => sorry
  termination_by structural c

@[aesop 10%] def ThinW.conv {Γ : ConE γ} {Δ' Δ : ConE δ} {σ} (c : ConWConv Δ' Δ) (σw : ThinW Γ Δ σ) : ThinW Γ Δ' σ :=
  match δ, Δ', Δ, σ, σw with
  | 0  , .nil      , .nil    , .nil    , .nil Γw => .nil Γw
  | 0  , .nil      , .nil    , .wk σ   , .wk Γw Δw Ww σw => .wk Γw Δw Ww σw
  | δ+1, .ext Δ' A', .ext Δ A, .wk σ   , .wk Γw Δw Ww σw => .wk Γw c.w_left Ww (ThinW.conv c σw)
  | δ+1, .ext Δ' A', .ext Δ A, .lift σ , .lift Γw Δw Ww σw => sorry

mutual
  @[aesop 50%] def VarW.ren {Γ : ConE γ} {Δ : ConE δ} {A v σ} (Γw : ConW Γ) (Δw : ConW Δ) (Aw : TyW Δ A) (vw : VarW Δ A v) (σw : ThinW Γ Δ σ)
    : VarW Γ (A.ren σ) (v.ren σ)
  :=
    match γ, Γ, Γw, δ, Δ, Δw, A, Aw, v, vw, σ, σw with
    | γ+1, Γ;W, .ext Γw Ww, δ, Δ, Δw, A, Aw, v, vw                , .wk σ, .wk _ _ _ σw => by
      have : δ > 0 := by cases v <;> omega
      let ih : Γ ⊢ A⌊σ⌋ := (TyW.ren Γw Δw Aw σw)
      -- by
      rw [VarE.ren]
      rw [<- ThinE.comp_wki]
      rw [<- TyE.ren_comp]
      exact VarW.vs Γw ih Ww (VarW.ren Γw Δw Aw vw σw)
    | γ+1, Γ; .(W⌊σ⌋), .ext Γw _, δ+1, Δ;W, .ext Δw Ww, .(W⌊wki⌋), Wwkiw, .vz, @VarW.vz .(δ) .(Δ) .(W) .(Δw) .(Ww)      , _, @ThinW.lift _ _ .(Γ) _ _ σ _ _Δw _Ww σw => by -- ⊢ `VarW (Γ; W[σ]) A[lift σ] _`, note that `A = W[wki]` due to `.vz`
      -- here, Lean is able to give us a goal of `⊢ VarW (Γ; W[σ]) W[wki][lift σ] _`
      rw [VarE.ren]
      rw [TyE.ren_comp, ThinE.wki, ThinE.comp, ThinE.id_comp]
      have res := VarW.vz Γw (TyW.ren Γw Δw Ww σw)
      rw [TyE.ren_comp, ThinE.wki, ThinE.comp, ThinE.comp_id] at res
      exact res
    | γ+1, Γ; .(B⌊σ⌋), .ext Γw _, δ+1, Δ; B, .ext Δw Bw, .(A⌊.wki⌋), _, .vs v, @VarW.vs .(δ) .(Δ) A .(B) .(v) .(Δw) Aw .(Bw) vw, _, @ThinW.lift _ _ .(Γ) _ _ σ .(Γw) _Δw Ww σw => by
      rw [VarE.ren]
      rw [TyE.ren_comp, ThinE.wki, ThinE.comp, ThinE.id_comp]
      have res := VarW.vs Γw (TyW.ren Γw Δw Aw σw) (TyW.ren Γw Δw Bw σw) (VarW.ren Γw Δw Aw vw σw)
      rw [TyE.ren_comp, ThinE.wki, ThinE.comp, ThinE.comp_id] at res
      exact res
    | 0, .nil, .nil, 0, .nil, .nil, _, _, v, vw, σ, σw => nomatch v
  termination_by (σ.amount_wk + Δ.size + A.size, 0)

  /-- `substTy {Γ Δ : Con} (A : Ty Δ) (σ : Subst Γ Δ) : Ty Γ` -/
  @[aesop 50%] def TyW.ren {σ : ThinE γ δ} (Γw : ConW Γ) (Δw : ConW Δ) (Aw : TyW Δ A) (σw : ThinW Γ Δ σ) : TyW Γ (A.ren σ) :=
    match A, Aw with
    | .U      , .U Δw        => .U Γw
    | .El t   , .El Δw tw    => .El Γw (TmW.ren Γw Δw (.U Δw) tw σw)
    | .Pi A B , .Pi Δw Aw Bw =>
      .Pi Γw (TyW.ren Γw Δw Aw σw) (TyW.ren (.ext Γw (TyW.ren Γw Δw Aw σw)) (.ext Δw Aw) Bw (.lift Γw Δw Aw σw))
    | .Sum A B, .Sum Δw Aw Bw => .Sum Γw (TyW.ren Γw Δw Aw σw) (TyW.ren Γw Δw Bw σw)
    | .Unit   , .Unit Δw      => .Unit Γw
  termination_by (σ.amount_wk + Δ.size + A.size, sizeOf A)
  decreasing_by
    . decreasing_tactic
    . decreasing_tactic
    . have l : amount_wk (lift σ) + ConE.size (Δ; A) + TyE.size B = amount_wk σ + ConE.size Δ + TyE.size (TyE.Pi A B) := by rw [amount_wk, ConE.size, TyE.size]; omega
      rw [l]
      have r : sizeOf B < sizeOf (TyE.Pi A B) := by decreasing_tactic
      exact Prod.Lex.right _ r -- Lean for some reason isn't able to figure this out on its own
    . decreasing_tactic
    . decreasing_tactic
    done

  /-- `Tm.thin {Γ Δ : Con} {A : Ty Δ} (t : Tm Δ A) (σ : Subst Γ Δ) : Tm Γ A[σ]` -/
  @[aesop 50%] def TmW.ren {σ : ThinE γ δ} (Γw : ConW Γ) (Δw : ConW Δ) (Xw : TyW Δ X) (tw : TmW Δ X t) (σw : ThinW Γ Δ σ)
    : TmW Γ (X.ren σ) (t.ren σ)
    :=
      match tw with
      | .var Δw Aw vw => .var Γw (TyW.ren Γw Δw Aw σw) (VarW.ren Γw Δw Aw vw σw)
      | .app Δw Aw Bw fw aw => by
        rw [TmE.ren]
        have res := TmW.app
          Γw
          (TyW.ren Γw Δw Aw σw)
          (TyW.ren (.ext Γw (TyW.ren Γw Δw Aw σw)) (.ext Δw Aw) Bw (.lift Γw Δw Aw σw))
          (TmW.ren Γw Δw (.Pi Δw Aw Bw) fw σw)
          (TmW.ren Γw Δw Aw aw σw)
        simp_all only [TyE.ren_toSubst, lift_toSubst, TmE.ren_toSubst, TyE.subst_comp, SubstE.comp, SubstE.lift, SubstE.id_comp, TmE.subst, VarE.subst]
        rw [<- SubstE.comp_wki] at res -- we can use our theorems on erased terms here :)
        rw [<- SubstE.comp_assoc] at res
        simp_all
      | .lam .. => sorry
      | @TmW.conv _ Δ' Δ A' A t' Δ'w Δw A'w Aw Δc Ac t'w => by
        have σ'w : ThinW Γ Δ' _ := ThinW.conv Δc σw
        have Aσ_conv : Γ ⊢ A'⌊σ⌋ ≅ A⌊σ⌋ := TyWConv.thin Γw σ'w Ac
        have ih : (Γ ⊢ t'⌊σ⌋ : A'⌊σ⌋) := TmW.ren Γw Δ'w A'w t'w σ'w
        have Aσw : Γ ⊢ A⌊σ⌋ := Aσ_conv.w_right
        have A'σw : Γ ⊢ A'⌊σ⌋ := Aσ_conv.w_left
        exact TmW.conv Γw Γw A'σw Aσw (.refl Γw) Aσ_conv ih
        done
      | .unit .. => sorry
      | .left .. => sorry
      | .right .. => sorry
      | .pi .. => sorry
      | .elimSum Δw Aw Bw Mw lw rw tw => by sorry
  termination_by (σ.amount_wk + Δ.size + t.size, sizeOf t)
  decreasing_by
    . sorry
    . sorry
    . decreasing_tactic
    . sorry
    . decreasing_tactic
    . decreasing_tactic
    . sorry
end


@[aesop 50%] def SubstW.compST (Γw : ConW Γ) : SubstW Θ Δ σ₁ → ThinW Γ Θ σ₂ → SubstW Γ Δ (SubstE.compST σ₁ σ₂)
| .nil ..                                 , σ₂w => .nil Γw
| .cons (A := A) (σ := σ₁) (t := t) Θw Δw Aw σ₁w tw, σ₂w => by
  rw [SubstE.compST]
  have ih_σ := SubstW.compST Γw σ₁w σ₂w
  have ih_t : TmW Γ A[σ₁]⌊σ₂⌋ t⌊σ₂⌋ := TmW.ren Γw Θw sorry tw σ₂w -- we should be able to get `Θ ⊢ A[σ₁]` from `tw : (Θ ⊢ t : A[σ₁])`
  have : A[σ₁]⌊σ₂⌋ = A[σ₁ ∘ᵀ σ₂] := by grind only [= TyE.ren_subst, = TmE.ren_toSubst, =_ SubstE.compST_toSubst, = TyE.ren_toSubst, =_ TyE.subst_ren_comp]
  rw [this] at ih_t
  have ret := SubstW.cons Γw Δw Aw ih_σ ih_t
  exact ret

@[aesop 90%] def SubstW.wk {Γ : ConE γ} {Δ : ConE δ} (Ww : TyW Γ W) (σw : SubstW Γ Δ σ) : SubstW (.ext Γ W) Δ (.wk σ) := by
  rw [SubstE.wk]
  have Γw := Ww.w_con
  have r := ThinW.wki Γw Ww
  exact SubstW.compST (Γw.ext Ww) σw r

@[aesop 50%] theorem SubstW.w_con_left : {Δ : ConE δ} -> SubstW Γ Δ σ -> ConW Γ
| .nil, .nil Γw => Γw
| .ext Δ A, .cons Γw Δw .. => Γw
@[aesop 50%] theorem SubstW.w_con_right : {Δ : ConE δ} -> SubstW Γ Δ σ -> ConW Δ
| .nil, .nil Γw => .nil
| .ext Δ A, .cons Γw Δw Aw .. => Δw.ext Aw

@[aesop 90%] def SubstW.lift {Γ : ConE γ} {Δ : ConE δ} (Ww : TyW Δ W) (σw : SubstW Γ Δ σ) : SubstW (.ext Γ (W.subst σ)) (.ext Δ W) (.lift σ) := by
  rw [SubstE.lift]
  have Δw := Ww.w_con
  have Γw : ConW Γ := σw.w_con_left
  have Wσw : TyW Γ W[σ] := sorry
  have Wσw_wki : TyW (Γ; W[σ]) W[σ]⌊wki⌋ := TyW.ren (Γw.ext Wσw) Γw Wσw (.wki Γw Wσw)
  have h := VarW.vz Γw Wσw
  have : W[σ]⌊wki⌋ = W[.wk σ] := by grind only [= TyE.subst_ren_comp, = TyE.ren_subst, =_ SubstE.compRen_wki, = TyE.ren_toSubst, =_ SubstE.comp_wki, SubstE.wk, wki]
  rw [this] at Wσw_wki -- Using E theorems
  rw [this] at h
  have res := SubstW.cons (Γw.ext Wσw) Δw Ww (SubstW.wk Wσw σw) (.var (Γw.ext Wσw) Wσw_wki h)
  exact res

@[aesop 90%] def SubstW.id : {Γ : ConE γ} -> ConW Γ -> SubstW Γ Γ .id
| .nil, .nil => .nil .nil
| .ext Γ A, .ext Γw Aw => by
  have ih := id Γw
  have ihl := ih.lift Aw
  have : A[.id] = A := TyE.subst_id A -- We can use our -E theorems here :) !
  rw [this] at ihl
  exact ihl

@[aesop 1%] def SubstW.wki : TyW Γ W -> SubstW (.ext Γ W) Γ .wki := by
  intro a_1
  simp_all only [SubstE.wki]
  apply SubstW.wk
  · simp_all only
  · apply SubstW.id
    apply TyW.w_con
    · exact a_1

@[aesop 50%] def VarW.subst (Γw : ConW Γ) (Δw : ConW Δ) (Aw : TyW Δ A) (vw : VarW Δ A v) (σw : SubstW Γ Δ σ) : TmW Γ (A.subst σ) (v.subst σ) := sorry

@[aesop 50%] def TyWConv.subst {Γ:ConE γ} {Δ:ConE δ} {X Y : TyE δ}
  (Γw : ConW Γ) (σw : SubstW Γ Δ σ) (c : Δ ⊢ X ≅ Y) : Γ ⊢ X[σ] ≅ Y[σ]
  :=
  match h : c with
  | @TyWConv.refl _ Δ A Δw Aw => sorry
  | @TyWConv.symm _ Δ X Y c => sorry
  | @TyWConv.trans _ Δ X Y Z Δw Xw Yw Zw c1 c2 => sorry
  | @TyWConv.U _ Δ Δw => by
    rw [TyE.subst]
    exact TyWConv.refl Γw (.U Γw)
  | @TyWConv.Pi _ Δ A A' B B' Δw Aw A'w Bw B'w Ac Bc =>
    have ihA  : Γ        ⊢ A[σ]       ≅ A'[σ]       := TyWConv.subst Γw σw Ac
    have Aσw  : Γ        ⊢ A[σ]                     := ihA.w_left
    have A'σw : Γ        ⊢ A'[σ]                    := ihA.w_right
    have ihB  : Γ; A[σ]  ⊢ B[.lift σ] ≅ B'[.lift σ] := TyWConv.subst (Γw.ext Aσw) (σw.lift Aw) Bc
    have Bσw  : Γ; A[σ]  ⊢ B[.lift σ]               := ihB.w_left
    have B'σw : Γ; A'[σ] ⊢ B'[.lift σ]              := TyW.conv ((ConWConv.refl Γw).ext ihA) (ihB.w_right)
    by
      rw [TyE.subst, TyE.subst]
      exact @TyWConv.Pi _ Γ A[σ] A'[σ] B[.lift σ] B'[.lift σ] Γw Aσw A'σw Bσw B'σw ihA ihB
  | @TyWConv.El _ Δ t t' Δw tw t'w c => sorry
  termination_by structural c

@[aesop 1%] def SubstW.conv {Γ : ConE γ} {Δ' Δ : ConE δ} {σ} (c : ConWConv Δ' Δ) (σw : SubstW Γ Δ σ) : SubstW Γ Δ' σ :=
  match δ, Δ', Δ, σ, σw with
  | 0  , .nil      , .nil    , .nil     , @SubstW.nil .(γ) .(Γ) Γw => .nil Γw
  | δ+1, .ext Δ' A', .ext Δ A, .cons σ t, @SubstW.cons .(γ) .(Γ) .(δ) .(Δ) .(A) .(σ) .(t) Γw Δw Aw σw tw =>
    match c with
    | .refl .. => .cons Γw Δw Aw σw tw
    | .symm .. => sorry
    | .trans .. => sorry
    | .ext Δc Ac =>
      have ih := SubstW.conv Δc σw
      have h : Δ ⊢ A ≅ A' := TyWConv.conv Δc Ac.symm
      SubstW.cons Γw Δc.w_left Ac.w_left ih (tw.conv_easy (.refl Γw) (TyWConv.subst Γw σw h))

mutual
  /-- `Ty.subst {Γ Δ : Con} (A : Ty Δ) (σ : Subst Γ Δ) : Ty Γ` -/
  @[aesop safe] def TyW.subst (Γw : ConW Γ) (Δw : ConW Δ) (Aw : TyW Δ A) (σw : SubstW Γ Δ σ) : TyW Γ (A.subst σ) :=
    match Aw with
    | .U Δw => .U Γw
    | .Pi Δw Aw Bw =>
      let Aσw := TyW.subst Γw Δw Aw σw
      .Pi Γw Aσw (TyW.subst (.ext Γw Aσw) (.ext Δw Aw) Bw (σw.lift Aw))
    | .El Δw tw => .El Γw (TmW.subst Γw Δw (.U Δw) tw σw)
    | .Sum Δw Aw Bw => .Sum Γw (TyW.subst Γw Δw Aw σw) (TyW.subst Γw Δw Bw σw)
    | .Unit Δw => .Unit Γw
    termination_by structural Aw

  /-- `Tm.subst {Γ Δ : Con} {A : Ty Δ} (t : Tm Δ A) (σ : Subst Γ Δ) : Tm Γ A[σ]` -/
  @[aesop safe] def TmW.subst (Γw : ConW Γ) (Δw : ConW Δ) (Aw : TyW Δ A) (tw : TmW Δ A t) (σw : SubstW Γ Δ σ) : TmW Γ (A.subst σ) (t.subst σ) :=
    match h : tw with
    | .var Δw Xw vw => VarW.subst Γw Δw Aw vw σw
    | @TmW.app _ Δe Ae Be fe ae Δw Aw Bw fw aw => by
      have Aσw := Aw.subst Γw Δw σw
      have Bσw := Bw.subst (Γw.ext Aσw) (Δw.ext Aw) (σw.lift Aw)
      have fσw := fw.subst Γw Δw (.Pi Δw Aw Bw) σw
      have aσw := aw.subst Γw Δw Aw σw
      have := @TmW.app _ Γ (Ae.subst σ) (Be.subst σ.lift) (fe.subst σ) (ae.subst σ) Γw Aσw Bσw fσw aσw
      rw [<- TmE.subst] at this
      rw [TyE.subst_comp] at this
      rw [TyE.subst_comp]
      rw [SubstE.comp]
      rw [SubstE.lift] at this
      rw [SubstE.comp] at this
      rw [TmE.subst, VarE.subst] at this
      rw [SubstE.comp_wk_cons] at this
      rw [SubstE.id_comp]
      exact this
    | .lam Δw Aw Bw bw => by
      have Aσw := Aw.subst Γw Δw σw
      have Bσw := Bw.subst (Γw.ext Aσw) (Δw.ext Aw) (σw.lift Aw)
      have bσw := bw.subst (Γw.ext Aσw) (Δw.ext Aw) Bw (σw.lift Aw)
      exact TmW.lam Γw Aσw Bσw bσw
    | @TmW.conv _ Δ' Δ A' A t' Δ'w Δw A'w Aw Δc Ac t'w  => by -- note that we *can* deal with the extra `TmW.conv` constructor here!
      have σ'w : SubstW Γ Δ' σ := SubstW.conv Δc σw
      have Aσ_conv : Γ ⊢ A'[σ] ≅ A[σ] := TyWConv.subst Γw σ'w Ac
      have ih : (Γ ⊢ t'[σ] : A'[σ]) := TmW.subst Γw Δ'w A'w t'w σ'w
      subst A Δ t'
      cases h
      have Aσw : Γ ⊢ A[σ] := Aσ_conv.w_right
      have A'σw : Γ ⊢ A'[σ] := Aσ_conv.w_left
      exact TmW.conv Γw Γw A'σw Aσw (.refl Γw) Aσ_conv ih
      done
    | .pi _ _ _ => sorry
    | .unit _  => sorry
    | .right _ _ _ _  => sorry
    | .left _ _ _ _ => sorry
    | .elimSum _ _ _ _ _ _ _  => sorry
    termination_by structural tw
end

/-- `comp {Γ Θ Δ : Con} : Subst Θ Δ -> Subst Γ Θ -> Subst Γ Δ` -/
def SubstW.comp (Γw : ConW Γ) (Θw : ConW Θ) (Δw : ConW Δ) (δw : SubstW Θ Δ δ) (σw : SubstW Γ Θ σ) : SubstW Γ Δ (.comp δ σ) := by
  cases δ <;> cases δw
  case nil => exact .nil Γw
  case cons =>
    expose_names
    rw [SubstE.comp]
    have ih_σ := SubstW.comp Γw Θw h h_3 σw
    have ih_t := TmW.subst Γw h_2 (TyW.subst Θw h h_1 h_3) h_4 σw
    rw [TyE.subst_comp] at ih_t
    have ret := SubstW.cons Γw h h_1 ih_σ ih_t
    aesop (add 50% apply [SubstE.cons, TyE.subst_comp, TmE.subst_comp])

theorem ConW.cast (Γw : ConW Γ) (Δw : ConW Δ) (h : ConWConv Γ Δ) : ConW Γ = ConW Δ := by
  ext; constructor <;> (intro; assumption)

theorem TyW.cast (Γw : ConW Γ) (Δw : ConW Δ) (h : ConWConv Γ Δ) : TyW Γ A = TyW Δ A := by
  ext; constructor
  . exact fun l => TyW.conv h l
  . exact fun r => TyW.conv h.symm r

theorem TmW.cast (Γw : ConW Γ) (Aw : TyW Γ A) (Bw : TyW Γ B) (h : TyWConv Γ A B) : TmW Γ A t = TmW Γ B t
  := propext ⟨ .conv Γw Γw Aw Bw (.refl Γw) h, .conv Γw Γw Bw Aw (.refl Γw) h.symm ⟩

@[aesop forward norm] theorem VarW.con_wf : VarW Γ X t -> ConW Γ
| .vz Γw Aw => .ext Γw Aw
| .vs Γw Aw Bw vw => .ext Γw Bw

@[aesop forward norm] theorem VarW.ty_wf : VarW Γ X t -> TyW Γ X
| .vz Γw Aw => by
  simp_all only [wki, TyE.ren_toSubst, wk_toSubst, id_toSubst]
  exact Aw.subst (.ext Γw Aw) Γw (.wki Aw)
| .vs Γw Aw Bw vw => by
  simp_all only [wki, TyE.ren_toSubst, wk_toSubst, id_toSubst]
  exact Aw.subst (.ext Γw Bw) Γw (.wki Bw)


/-
  # Meta-theoretic properties
  Inversion, injectivity
-/

theorem TmW.lam_inv (tw : TmW Γ X (TmE.lam A B body)) : TyWConv Γ X (.Pi A B) := impl tw rfl
where impl {γ} {Γ : ConE γ} {X A B body} {LAM} (tw : TmW Γ X LAM) (h : LAM = .lam A B body) : TyWConv Γ X (.Pi A B) :=
  match tw with
  | .lam Γw Aw Bw bodyw => by
    cases h
    exact .refl Γw (.Pi Γw Aw Bw)
  | @TmW.conv .(γ) Γ' .(Γ) X' X (.lam A_ B_ body_) Γ'w Γw X'w Xw Γc Xc t'w => by
    clear tw
    have ih : TyWConv Γ' X' (.Pi A_ B_) := impl (LAM := .lam A_ B_ body_) t'w rfl -- terminates structurally because `t'w < .conv ... t'w`
    have hA : A = A_ := by simp_all only [TmE.lam.injEq]
    subst hA
    have hB : B = B_ := by simp_all only [TmE.lam.injEq, true_and]
    subst hB
    have hbody : body = body_ := by simp_all only [TmE.lam.injEq, true_and]
    subst hbody
    clear h
    have ⟨A'w, B'w, body'w⟩ := TmW.lam_wf t'w
    have : TyWConv Γ' X (TyE.Pi A B) := TyWConv.trans Γ'w (TyW.conv Γc.symm Xw) X'w ih.w_right Xc.symm ih
    exact @TyWConv.conv _ Γ' Γ X (.Pi A B) Γc this
termination_by structural tw

#print axioms TmW.lam_inv -- only propext

theorem TmW.app_inv (tw : TmW Γ X (TmE.app A B f a)) : TyWConv Γ X (B.subst (.cons .id a)) :=
  have ⟨Aw, Bw, fw, aw⟩ := TmW.app_wf tw
  match tw with
  | .app Γw Aw Bw fw aw => .refl Γw (TyW.subst Γw (.ext Γw Aw) Bw (.cons Γw Γw Aw (.id Γw) (TyE.subst_id _ ▸ aw)))
  | @TmW.conv _ Γ' .(Γ) X' .(_) _ Γ'w Γw X'w Xw Γc Xc tw => by sorry

theorem TmW.pi_inv (tw : TmW Γ X (TmE.pi A B)) : TyWConv Γ X .U := sorry

theorem TmW.unit_inv (tw : TmW Γ X (.unit)) : TyWConv Γ X .Unit := sorry

theorem VarW.inv (vw : VarW Γ X v) : X = v.getType Γ := by -- We have actual equality, not just `TyWConv`.
  match vw with
  | .vz Γw Aw => simp_all only [TyE.ren_toSubst, wki_toSubst]; rfl
  | .vs Γw Aw Bw vw => rw [VarW.inv vw]; simp_all only [TyE.ren_toSubst, wki_toSubst]; rfl

theorem VarW.vs_wf (vw : VarW (Γ; B) X (.vs v)) : VarW Γ (v.getType Γ) v :=
  match vw with
  | VarW.vs (A := A) Γw Aw Bw vw => by rwa [<- VarW.inv vw]

theorem VarW.vs_inv (vw : VarW (Γ; B) X (.vs v)) : TyWConv (Γ; B) X ((v.getType Γ).ren .wki) := by
  cases h : vw
  case vs γ A Γw Aw Bw vw => sorry

theorem TmW.var_wf (w : TmW Γ X (.var v)) : VarW Γ X v :=
  impl w rfl
where impl {γ} {Γ : ConE γ} {X VAR v} (w : TmW Γ X VAR) (h : VAR = (.var v)) : VarW Γ X v :=
  match w with
  | TmW.var Γw Xw vw => by
    cases h
    exact vw
  | @TmW.conv .(γ) Γ' .(Γ) X' X (.var v_) Γ'w Γw X'w Xw Γc Xc w' => by
    let w := impl (VAR := TmE.var v_) w' rfl
    have hv : v = v_ := by simp_all only [TmE.var.injEq]
    -- subst hv
    -- let Aw    := TyW.conv' Γ'w Γw Γc A_w
    -- let Bw    := TyW.conv' (Γ := Γ'.ext A) (Δ := Γ.ext A) (Γ'w.ext A_w) (Γw.ext Aw) (Γc.ext (.refl Γ'w A_w)) B_w
    -- let bodyw := TmW.conv_easy (Γc.ext (.refl Γ'w A_w)) (.refl (.ext Γ'w A_w) B_w) body_w
    have : VarW Γ' X' v = VarW Γ X v := sorry -- okay because of uniqueness of indices in VarW
    exact this ▸ (hv ▸ w)
  termination_by structural w

axiom TyE.Pi.inj_conv : TyWConv Γ (.Pi A₁ B₁) (.Pi A₂ B₂) -> TyWConv Γ A₁ A₂ ∧ TyWConv (Γ.ext A₁) B₁ B₂
