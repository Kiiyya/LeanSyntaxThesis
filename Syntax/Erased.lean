import Aesop
import Qq
import Lean

set_option linter.unusedVariables false
set_option pp.fieldNotation.generalized false

/-
  # Erased
-/

mutual
  @[aesop 1%]
  inductive ConE : Nat -> Type
  | nil : ConE 0
  | ext : ConE γ -> TyE γ -> ConE (γ + 1)
  deriving Repr

  /-- `Ty : Con -> Type` -/
  @[aesop 1%]
  inductive TyE : Nat -> Type
  /-- `U Γ : Ty Γ` -/
  | U : TyE γ
  /-- `El {Γ} : (t : Tm Γ U) -> Ty Γ` -/
  | El : TmE γ -> TyE γ
  /-- `Ty.Pi {Γ} : (A : Ty Γ) -> (B : Ty (Γ; A)) -> Ty Γ` -/
  | Pi : (A : TyE γ) -> (B : TyE (γ + 1)) -> TyE γ
  | Sum : TyE γ -> TyE γ -> TyE γ
  | Unit : TyE γ
  deriving Repr

  /-- `Var : (Γ : Con) -> Ty Γ -> Type` -/
  @[aesop 1%]
  inductive VarE : Nat -> Type
  /-- `vz {Γ} {A : Ty Γ} : Var (Γ, A) A[wki]`, note that `wki : Subst (Γ, A) Γ` -/
  | vz : VarE (γ + 1)
  /-- `vs {Γ} {A : Ty Γ} {B : Ty Γ} : Var Γ A -> Var (Γ; B) A[wki]` -/
  | vs : VarE γ -> VarE (γ + 1)
  deriving Repr

  /-- `Tm : (Γ : Con) -> Ty Γ -> Type` -/
  @[aesop 1%]
  inductive TmE : Nat -> Type
  /-- `var {Γ} {A : Ty Γ} : Var Γ A -> Tm Γ A` -/
  | var : VarE γ -> TmE γ
  /-- `app {Γ : Con} {A : Ty Γ} {B : Ty (Γ, A)} : (f : Tm Γ (Pi A B)) -> (a : Tm Γ A) -> Tm Γ B[⟨id, a⟩]`.\
    Note that the substitution `⟨id, a⟩ : Subst Γ (Γ; A)` intuitively instantiates de-Bruijn variable #0 with `a : Tm Γ A`.  -/
  | app : (A : TyE γ) -> (B : TyE (γ + 1)) -> (f : TmE γ) -> (a : TmE γ) -> TmE γ
  /-- `lam {Γ} {A : Ty Γ} {B : Ty (Γ, A)} : (body : Tm (Γ, A) B) -> Tm Γ (Pi A B)` -/
  | lam : (A : TyE γ) -> (B : TyE (γ + 1)) -> (body : TmE (γ + 1)) -> TmE γ
  /-- `Tm.Pi {Γ} : (A : Tm Γ .U) -> (B : Tm (Γ; A) .U) -> Tm Γ .U` -/
  | pi : (A : TmE γ) -> (B : TmE (γ + 1)) -> TmE γ
  /-- `Tm.left {Γ A B} : Tm Γ A -> Tm Γ (Sum A B)` -/
  | left : TmE γ -> TmE γ
  /-- `Tm.right {Γ A B} : Tm Γ B -> Tm Γ (Sum A B)` -/
  | right : TmE γ -> TmE γ
  /--
    ```
    Tm.elimSum {Γ : Con} {A B : Ty Γ} :
      (Mot : Tm (Γ; "Sum A B") .U) ->
      (leftM  : Tm (Γ; A) Mot["left #0"]) ->
      (rightM : Tm (Γ; B) Mot["right #0"]) ->
      (t : Tm Γ "Sum A B") ->
      Tm Γ Mot[t]
    ``` -/
  | elimSum : (A B : TyE γ) -> (Mot : TyE (γ + 1)) -> (leftM : TmE (γ + 1)) -> (rightM : TmE (γ + 1)) -> (t : TmE γ) -> TmE γ
  | unit : TmE γ
  deriving Repr

  /-- Thinnings. -/
  @[aesop 1%]
  inductive ThinE : Nat -> Nat -> Type
  /-- `Thin.nil {Γ} : Thin Γ []` -/
  | nil : ThinE γ 0
  | wk   : ThinE γ δ -> ThinE (γ + 1) δ
  | lift : ThinE γ δ -> ThinE (γ + 1) (δ + 1)

  /-- A substitution `σ : Subst Γ Δ` maps every variable in `Δ` to a `Γ`-term. -/
  @[aesop 1%]
  inductive SubstE : Nat -> Nat -> Type
  /-- `Subst.nil {Γ} : Subst Γ []` -/
  | nil : SubstE γ 0
  /-- `Subst.cons {Γ Δ} {A : Ty Δ} : (σ : Subst Γ Δ) -> (t : Tm Γ A[σ]) -> Subst Γ (Δ; A)` -/
  | cons : SubstE γ δ -> TmE γ -> SubstE γ (δ + 1)
  deriving Repr
end

namespace Erased.Notation
  scoped notation "[]" => ConE.nil
  scoped infixl:66 "; " => ConE.ext
end Erased.Notation
open Erased.Notation

@[simp] def VarE.toNat : VarE γ -> Nat
| .vz => 0
| .vs v => .succ v.toNat

@[simp, grind]
def VarE.ren : {γ δ : Nat} -> VarE δ -> ThinE γ δ -> VarE γ
| γ+1, δ  , v              , @ThinE.wk   .(γ) .(δ) σ => .vs (VarE.ren v σ)
| γ+1, δ+1, @VarE.vz .(δ)  , @ThinE.lift .(γ) .(δ) σ => .vz
| γ+1, δ+1, @VarE.vs .(δ) v, @ThinE.lift .(γ) .(δ) σ => .vs (VarE.ren v σ)
| 0  , 0  , v              , @ThinE.nil    0          => nomatch v
termination_by structural γ δ v σ => σ


mutual
  /-- `Ty.thin {Γ Δ : Con} (A : Ty Δ) (σ : Thin Γ Δ) : Ty Γ` -/
  @[simp, grind]
  def TyE.ren {γ δ} : (A : TyE δ) -> ThinE γ δ -> TyE γ
  | .U, σ => .U
  | .El t, σ => .El (TmE.ren t σ)
  | .Pi A B, σ => -- `Δ ⊢ A`, `Δ;A ⊢ B`
    let Aσ    /- : `Ty Γ` -/                       := TyE.ren A σ -- `Γ ⊢ A[σ]`
    let wk_σ  /- : `Thin (Γ; A[σ]) Δ` -/       := ThinE.wk σ
    let lift_σ /- : `Thin (Γ; A[σ]) (Δ; A)` -/ := ThinE.lift σ
    .Pi Aσ (TyE.ren B lift_σ) -- `Γ ⊢ Pi A[σ] B[lift σ]`
  | .Sum A B, σ => .Sum (A.ren σ) (B.ren σ)
  | .Unit, σ => .Unit
  termination_by structural A σ => A

  /-- `Tm.thin {Γ Δ : Con} {A : Ty Δ} (t : Tm Δ A) (σ : Thin Γ Δ) : Tm Γ (Ty.thin A σ)` -/
  @[grind]
  def TmE.ren : TmE δ -> ThinE γ δ -> TmE γ
  | .var v      , σ => .var (VarE.ren v σ)
  | .app A B f a, σ => -- `Δ ⊢ a : A`, `Δ ⊢ f : Pi A B`, expected `Tm Γ B[⟨id, a⟩][σ]`
    let Aσ    /- : `Ty Γ` -/                       := TyE.ren A σ -- `Γ ⊢ A[σ]`
    let wk_σ  /- : `Thin (Γ; A[σ]) Δ` -/       := ThinE.wk σ
    let lift_σ /- : `Thin (Γ; A[σ]) (Δ; A)` -/ := ThinE.lift σ
    let B' /- : `Ty (Γ; A[σ])` -/ := TyE.ren B lift_σ
    let f' : TmE γ := TmE.ren f σ -- `f[σ] : Tm Γ (Pi A B)[σ]`, where `(Pi A B)[σ] = Pi A[σ] B[⟨wk σ, #0⟩]`
    let a' : TmE γ := TmE.ren a σ -- `a[σ] : Tm Γ A[σ]`
    let fa' : TmE γ := .app Aσ B' f' a' -- `.app f[σ] a[σ] : Tm Γ B[⟨wk σ, #0⟩][⟨id, a⟩]`
    fa' -- ! here we need `⟨wk σ, #0⟩ ∘ ⟨id, a⟩ = ⟨id, a⟩ ∘ σ` to typecheck.
  | .lam A B body, σ => -- `body : Tm (Δ;A) B`, expected `Tm Γ (Pi A B)[σ]`
    -- reminder: `lam {Γ} {A : Ty Γ} {B : Ty (Γ;A)} : (body : Tm (Γ;A) B) -> Tm Γ (Pi A B)`
    let Aσ    /- : `Ty Γ` -/                        := TyE.ren A σ -- `Γ ⊢ A[σ]`
    let wk_σ  /- : `Thin (Γ; A[σ]) Δ` -/        := ThinE.wk σ
    let lift_σ /- : `Thin (Γ; A[σ]) (Δ; A)` -/  := ThinE.lift σ
    let B_lift_σ /- : `Ty (Γ; A[σ])` -/              := TyE.ren B    lift_σ -- `Δ; A ⊢ B` therefore `Γ; A[σ] ⊢ B[lift σ]`
    let body_lift_σ /- : `Tm (Γ; A[σ]) B[lift σ]` -/ := TmE.ren body lift_σ
    .lam Aσ B_lift_σ body_lift_σ
  | .pi A B, σ =>
    let Aσ    /- : `Ty Γ` -/                        := TmE.ren A σ -- `Γ ⊢ A[σ]`
    let wk_σ  /- : `Thin (Γ; A[σ]) Δ` -/        := ThinE.wk σ
    let lift_σ /- : `Thin (Γ; A[σ]) (Δ; A)` -/  := ThinE.lift σ
    let B_lift_σ /- : `Ty (Γ; A[σ])` -/              := TmE.ren B    lift_σ -- `Δ; A ⊢ B` therefore `Γ; A[σ] ⊢ B[lift σ]`
    .pi Aσ B_lift_σ
  | .left a, σ => .left (a.ren σ)
  | .right b, σ => .right (b.ren σ)
  | .elimSum A B Mot l r t, σ =>
    .elimSum (A.ren σ) (B.ren σ) (Mot.ren σ.lift) (l.ren σ.lift) (r.ren σ.lift) (t.ren σ)
  | .unit, σ => .unit
  termination_by structural t σ => t
end

/-- `Thin.comp {Γ Θ Δ : Con} : Thin Θ Δ -> Thin Γ Θ -> Thin Γ Δ`. -/
@[simp, grind] def ThinE.comp : {γ θ δ : Nat} -> (σ₁ : ThinE θ δ) → ThinE γ θ → ThinE γ δ
| γ+1, θ  , δ   , σ₁                       , @ThinE.wk   .(γ) .(θ) σ₂ => @ThinE.wk  γ δ  (ThinE.comp σ₁ σ₂)
| γ  , 0  , _   , .nil                     ,       .nil               => @ThinE.nil γ
| γ+1, θ+1, 0   , .nil                     , @ThinE.lift .(γ) .(θ) σ₂ => @ThinE.nil (γ+1)
| γ+1, θ+1, δ   , @ThinE.wk   .(θ) .(δ) σ₁ , @ThinE.lift .(γ) .(θ) σ₂ => @ThinE.wk   γ δ (ThinE.comp σ₁ σ₂)
| γ+1, θ+1, δ+1 , @ThinE.lift .(θ) .(δ) σ₁ , @ThinE.lift .(γ) .(θ) σ₂ => @ThinE.lift γ δ (ThinE.comp σ₁ σ₂)

attribute [simp] TmE.ren.eq_2
attribute [simp] TmE.ren.eq_3
attribute [simp] TmE.ren.eq_4
attribute [simp] TmE.ren.eq_5
attribute [simp] TmE.ren.eq_6
attribute [simp] TmE.ren.eq_7
attribute [simp] TmE.ren.eq_8
-- attribute [-simp] TmE.ren.eq_1
@[aesop norm] theorem TmE.ren_eq_1' : TmE.var (.ren v σ) = (TmE.var v).ren σ := Eq.symm (TmE.ren.eq_1 ..)

namespace Erased.Notation
  scoped notation:max (name := renVar) v:max "⌊" σ "⌋" => VarE.ren v σ
  scoped notation:max (name := renTy) A:max "⌊" σ "⌋" => TyE.ren A σ
  scoped notation:max (name := renTm) t:max "⌊" σ "⌋" => TmE.ren t σ
  scoped infixl:67 " ∘ " => ThinE.comp
end Erased.Notation

/-- `compST {Γ Θ Δ : Con} : Subst Θ Δ -> Thin Γ Θ -> Subst Γ Δ` -/
@[simp, grind]
def SubstE.compST : SubstE θ δ → ThinE γ θ → SubstE γ δ
| .nil         , σ₂ => .nil
| .cons σ₁ t   , σ₂ => -- `δ : Subst Θ Δ`,   `σ : Thin Γ Θ`,   `Θ ⊢ t : A[δ]`,
  .cons
    (SubstE.compST σ₁ σ₂) -- `δ ∘ σ : Subst Γ Δ`
    (TmE.ren t σ₂) -- `Γ ⊢ t[σ] : A[δ][σ]`, -- ! need theorem `A[δ][σ] = A[δ ∘ σ]` to typecheck

/-- `Var.subst {Γ Δ} {A : Ty Δ} (v : Var Δ A) (σ : Subst Γ Δ) : Tm Γ A[σ]`.\
  Look up the term stored in a substitution. -/
@[simp, grind]
def VarE.subst : VarE δ -> SubstE γ δ -> TmE γ
| .vz  , .cons _ t => t
| .vs v, .cons σ _ => VarE.subst v σ
termination_by structural v σ => v

@[aesop 5%, grind =] def ThinE.id : (γ : Nat) -> ThinE γ γ
| 0   => .nil
| γ+1 => .lift (@ThinE.id γ)

@[grind =] theorem ThinE.id_refold : ThinE.lift (.id γ) = .id _ := rfl

@[aesop norm, grind] def ThinE.wki : ThinE (γ + 1) γ := .wk (ThinE.id _)
@[aesop 5%, grind] def SubstE.wk (σ : SubstE γ δ) : SubstE (γ + 1) δ := SubstE.compST σ ThinE.wki

/-- `lift (W : Ty Δ) : (σ : Subst Γ Δ) -> Subst (Γ; W[σ]) (Δ; W)`. Defined as `lift σ := ⟨wk σ, #0⟩`. -/
@[aesop 5%, grind] def SubstE.lift (σ : SubstE γ δ) : SubstE (γ + 1) (δ + 1) := .cons (SubstE.wk σ) (.var .vz)

mutual
  /-- `Ty.subst {Γ : Con} {Δ : Con} (A : Ty Δ) (σ : Subst Γ Δ) : Ty Γ` -/
  @[simp, grind]
  def TyE.subst : TyE δ -> SubstE γ δ -> TyE γ
  | .U, σ => .U
  | .El t, σ => .El (.subst t σ)
  | .Pi A B, σ => .Pi (.subst A σ) (.subst B (.lift σ))
  | .Sum A B, σ => .Sum (.subst A σ) (.subst B σ)
  | .Unit, σ => .Unit
  termination_by structural A σ => A

  /-- `Tm.subst {Γ : Con} {Δ : Con} {A : Ty Δ} (t : Tm Δ A) (σ : Subst Γ Δ) : Tm Γ A[σ]` -/
  @[simp, grind]
  def TmE.subst : TmE δ -> SubstE γ δ -> TmE γ
  | .var v       , σ => VarE.subst v σ
  | .app A B f a , σ => .app (TyE.subst A σ) (TyE.subst B (SubstE.lift σ)) (TmE.subst f σ) (TmE.subst a σ) -- `.app f[σ] a[σ] : Tm Γ B[⟨wk σ, #0⟩][⟨id, a⟩]`
  | .lam A B body, σ => .lam (TyE.subst A σ) (TyE.subst B (SubstE.lift σ)) (TmE.subst body (SubstE.lift σ))
  | .pi A B      , σ => .pi (TmE.subst A σ) (TmE.subst B (SubstE.lift σ))
  | .left a, σ => .left (a.subst σ)
  | .right b, σ => .right (b.subst σ)
  | .elimSum A B Mot l r t, σ => .elimSum (A.subst σ) (B.subst σ) (.subst Mot σ.lift) (.subst l σ.lift) (.subst r σ.lift) (.subst t σ)
  | .unit, σ => .unit
  termination_by structural t σ => t
end

/-- `comp : Subst Θ Δ -> Subst Γ Θ -> Subst Γ Δ` -/
@[aesop 50%, grind]
def SubstE.comp : SubstE θ δ → SubstE γ θ → SubstE γ δ
| .nil     , σ => .nil
| .cons δ t, σ => -- `δ : Subst Θ Δ`,   `σ : Subst Γ Θ`,   `Θ ⊢ t : A[δ]`,   expected `Subst Γ (Δ; A)`
  .cons
    (SubstE.comp δ σ) -- δ ∘ σ : Subst Γ Δ
    (TmE.subst t σ) -- `Γ ⊢ t[σ] : A[δ][σ]`, -- ! need theorem `A[δ][σ] = A[δ ∘ σ]`
termination_by structural σ _ => σ

namespace Erased.Notation
  scoped notation:max (name := substVar) (priority := high) v:max "[" σ "]" => VarE.subst v σ
  scoped notation:max (name := substTy) (priority := high) A:max "[" σ "]" => TyE.subst A σ
  scoped notation:max (name := substTm) (priority := high) t:max "[" σ "]" => TmE.subst t σ
  scoped infixl:67 (name := stxCons) " ;; " => SubstE.cons
  scoped notation (name := stxNil) "⟨;;⟩" => SubstE.nil
  scoped infixl:67 (name := stxComp) " ∘ " => SubstE.comp
  scoped infixl:67 (name := stxCompRen) " ∘ᵀ " => SubstE.compST
end Erased.Notation

/-- Identity substitution. `id : {Γ : Con} -> Subst Γ Γ`. -/
@[aesop 5%, grind] def SubstE.id : {γ : Nat} -> SubstE γ γ
| 0     => .nil
| γ + 1 => SubstE.lift (@SubstE.id γ)

@[aesop norm, grind] def SubstE.wki : SubstE (γ + 1) γ := SubstE.wk SubstE.id


/-- Intuitively simply `Var.getType : Var Γ A -> Ty Γ := A`, but we reconstruct the type.
  ```
  Var.getType : {Γ : Con} -> {A : Ty Γ} -> Var Γ A -> Ty Γ
  | Γ;A, A[wki], (.vz   : Var (Γ;A) A[wki]) => A[wki]
  | Γ;B, A[wki], (.vs v : Var (Γ;B) A[wki]) => (@Var.getType Γ A[wki] v)[wki]
  ``` -/
def VarE.getType : {γ : Nat} -> (Γ : ConE γ) -> VarE γ -> TyE γ
| γ+1, .ext Γ A, .vz   => A.subst .wki
| γ+1, .ext Γ B, .vs v => (getType Γ v).subst .wki

@[aesop norm, grind =] theorem VarE.ren_comp {γ θ δ} (v : VarE δ) (σ₁ : ThinE θ δ) (σ₂ : ThinE γ θ) : VarE.ren (VarE.ren v σ₁) σ₂ = VarE.ren v (ThinE.comp σ₁ σ₂) := by
  match γ, θ, δ, v, σ₁, σ₂ with
  | γ  , θ  , .(0), v, @ThinE.nil  .(θ)        , σ₂                              => aesop? (add 1% cases [ThinE, VarE])
  | γ+1, θ+1, δ   , v, @ThinE.wk   .(θ) .(δ) σ₁, @ThinE.wk   .(γ) .(θ+1) σ₂ =>
    have ih := VarE.ren_comp v (.wk σ₁) σ₂
    rw [ThinE.comp]
    rw [VarE.ren]
    rw [VarE.ren]
    rw [VarE.ren]
    rw [<- VarE.ren_comp]
    rw [VarE.ren]
  | γ+1, θ+1, δ+1 , v, @ThinE.lift .(θ) .(δ) σ₁, @ThinE.wk   .(γ) .(θ+1) σ₂ =>
    rw [ThinE.comp]
    rw [VarE.ren]
    rw [VarE.ren]
    rw [<- VarE.ren_comp]
  | γ+1, θ+1, δ   ,  v,     @ThinE.wk   .(θ) .(δ) σ₁, @ThinE.lift .(γ) .(θ)   σ₂ =>
    rw [ThinE.comp]
    rw [VarE.ren]
    rw [VarE.ren]
    rw [<- VarE.ren_comp]
    rw [VarE.ren]
  | γ+1, θ+1, δ+1 , v,     @ThinE.lift .(θ) .(δ) σ₁, @ThinE.lift .(γ) .(θ)   σ₂ =>
    rw [ThinE.comp]
    cases v
    . rfl
    . rw [VarE.ren]
      rw [VarE.ren]
      rw [VarE.ren]
      rw [<- VarE.ren_comp]

@[aesop norm, grind =] theorem VarE.subst_comp {γ θ δ} (v : VarE δ) (σ₁ : SubstE θ δ) (σ₂ : SubstE γ θ) : TmE.subst (VarE.subst v σ₁) σ₂ = VarE.subst v (SubstE.comp σ₁ σ₂) := by
  match γ, θ, δ, v, σ₁, σ₂ with
  | _, _, _, .vz  , σ₁, σ₂ =>
    rename_i σ₁_1 σ₂_1 x x_1 γ_1
    cases σ₁_1 with
    | @nil γ_2 =>
      cases σ₂_1 with
      | @nil γ_2 =>
        rcases σ₁ with @⟨γ_2⟩ | @⟨γ_3, δ, a, a_1⟩
        cases σ₂ with
        | @nil γ_2 =>
          simp_all only [subst]
          rfl
        | @cons γ_3 δ a_2 a_3 =>
          simp_all only [subst]
          rfl
      | @cons γ_3 δ a a_1 =>
        rcases σ₁ with @⟨γ_2⟩ | @⟨γ_3, δ_1, a_2, a_3⟩
        cases σ₂ with
        | @nil γ_2 =>
          simp_all only [subst]
          rfl
        | @cons γ_3 δ_1 a_4 a_5 =>
          simp_all only [subst]
          rfl
    | @cons γ_3 δ_1 a a_1 =>
      cases σ₂_1 with
      | @nil γ_2 =>
        rcases σ₁ with @⟨γ_2⟩ | @⟨γ_3, δ, a_2, a_3⟩
        cases σ₂ with
        | @nil γ_2 =>
          simp_all only [subst]
          rfl
        | @cons γ_3 δ a_4 a_5 =>
          simp_all only [subst]
          rfl
      | @cons γ_3 δ a_2 a_3 =>
        rcases σ₁ with @⟨γ_2⟩ | @⟨γ_3, δ_2, a_4, a_5⟩
        cases σ₂ with
        | @nil γ_2 =>
          simp_all only [subst]
          rfl
        | @cons γ_3 δ_2 a_6 a_7 =>
          simp_all only [subst]
          rfl
  | _, _, _, .vs v, .cons σ₁ t, .nil =>
    rw [SubstE.comp]
    rw [VarE.subst]
    rw [VarE.subst]
    rw [subst_comp]
  | _, _, _, .vs v, .cons σ₁ t, .cons σ₂ u =>
    rw [SubstE.comp]
    rw [VarE.subst]
    rw [VarE.subst]
    rw [VarE.subst_comp]

mutual
  @[aesop norm, grind =] theorem TyE.ren_comp {γ θ δ : Nat} (A : TyE δ) (σ₂ : ThinE θ δ) (σ₁ : ThinE γ θ)
    : TyE.ren (TyE.ren A σ₂) σ₁ = TyE.ren A (ThinE.comp σ₂ σ₁)
    := by
    match A with
    | .U => rw [TyE.ren, TyE.ren, TyE.ren]
    | .El t => rw [TyE.ren, TyE.ren, TyE.ren, TmE.ren_comp]
    | .Pi A B =>
      rw [TyE.ren, TyE.ren, TyE.ren]
      /- ih_A : `A[δ][σ] = A[δ ∘ σ]` -/
      have ih_A : TyE.ren (TyE.ren A σ₂) σ₁ = TyE.ren A (ThinE.comp σ₂ σ₁) := TyE.ren_comp ..
      rw [ih_A]
      rw [TyE.ren_comp] -- ih_B : `B[lift δ][lift σ] = B[lift δ ∘ lift σ]`
      simp_all only [TyE.Pi.injEq, true_and]
      rfl
    | .Sum A B => rw [TyE.ren, TyE.ren, TyE.ren, TyE.ren_comp, TyE.ren_comp]
    | .Unit => rfl

  @[aesop norm, grind =] theorem TmE.ren_comp {γ θ δ} (t : TmE δ) (σ₂ : ThinE θ δ) (σ₁ : ThinE γ θ) : TmE.ren (TmE.ren t σ₂) σ₁ = TmE.ren t (ThinE.comp σ₂ σ₁) := by
    match t with
    | .var v => rw [TmE.ren, TmE.ren, TmE.ren, VarE.ren_comp]
    | .app A B f a =>
      rw [TmE.ren]
      rw [TmE.ren]
      rw [TmE.ren]
      rw [TmE.ren_comp f]
      rw [TmE.ren_comp a]
      rw [TyE.ren_comp A]
      rw [TyE.ren_comp B] -- `B[lift δ][lift σ] = B[lift δ ∘ lift σ]`
      rw [ThinE.comp]
    | .lam A B body =>
      rw [TmE.ren]
      rw [TmE.ren]
      rw [TmE.ren]
      rw [TmE.ren_comp body]
      rw [TyE.ren_comp A]
      rw [TyE.ren_comp B] -- `B[lift δ][lift σ] = B[lift δ ∘ lift σ]`
      rw [ThinE.comp]
    | .pi A B =>
      rw [TmE.ren]
      rw [TmE.ren]
      rw [TmE.ren]
      rw [TmE.ren_comp A]
      rw [TmE.ren_comp B] -- `B[lift δ][lift σ] = B[lift δ ∘ lift σ]`
      rw [ThinE.comp]
    | .left a => rw [TmE.ren, TmE.ren, TmE.ren, TmE.ren_comp]
    | .right b => rw [TmE.ren, TmE.ren, TmE.ren, TmE.ren_comp]
    | .elimSum A B Mot l r t =>
      rw [TmE.ren]
      rw [TmE.ren]
      rw [TmE.ren]
      rw [TyE.ren_comp]
      rw [TyE.ren_comp]
      rw [TyE.ren_comp]
      rw [TmE.ren_comp]
      rw [TmE.ren_comp]
      rw [TmE.ren_comp]
      rw [ThinE.comp]
      done
    | .unit => rfl
end

@[aesop norm, grind =, grind =_] theorem ThinE.comp_assoc {γ θ₁ θ₂ δ : Nat}
  {σ₁ : ThinE γ θ₁} {σ₂ : ThinE θ₁ θ₂} {σ₃ : ThinE θ₂ δ}
  : comp σ₃ (comp σ₂ σ₁) = comp (comp σ₃ σ₂) σ₁
  := by
    match γ, θ₁, θ₂, δ, σ₃, σ₂, σ₁ with
    | _, _, _, _, .nil    , .nil    , .nil     => rw [comp, comp, comp, comp]
    | _, _, _, _, σ₃      , σ₂      , .wk   σ₁ => rw [comp, comp, comp, comp_assoc]
    | _, _, _, _, .nil    , .nil    , .lift σ₁ => rw [comp, comp, comp]
    | _, _, _, _, σ₃      , .wk   σ₂, .lift σ₁ => rw [comp, comp, comp, comp, comp_assoc]
    | _, _, _, _, .wk   σ₃, .lift σ₂, .lift σ₁ => rw [comp, comp, comp, comp, comp_assoc]
    | _, _, _, _, .lift σ₃, .lift σ₂, .lift σ₁ => rw [comp, comp, comp, comp, comp_assoc]
    | _, _, _, _, .nil    , .lift σ₂, .lift σ₁ => rw [comp, comp, comp, comp]

@[simp, grind =] theorem ThinE.comp_id (σ : ThinE γ δ) : comp σ (id _) = σ := by
  match γ, σ with
  | 0, .nil => rfl
  | γ+1, .nil    => rfl
  | γ+1, .wk   σ => rw [ThinE.id, ThinE.comp, ThinE.comp_id]
  | γ+1, .lift σ => rw [ThinE.id, ThinE.comp, ThinE.comp_id]

@[simp, grind =] theorem ThinE.id_comp : {γ δ : Nat} -> (σ : ThinE γ δ) -> comp (id _) σ = σ
| _, _, .nil    => by rw [id, comp]
| _, _, .wk   σ => by rw [comp, id_comp]
| _, _, .lift σ => by rw [id, comp, id_comp]

/-- `σ ∘ wki = wk σ` -/
@[simp, grind =, grind =_] theorem ThinE.comp_wki (σ : ThinE γ δ) : comp σ wki = .wk σ := by rw [wki, comp, comp_id]
/-- `σ ∘ wk id = wk σ` -/
@[simp, grind =, grind =_] theorem ThinE.comp_wk_id (σ : ThinE γ δ) : comp σ (.wk (.id _)) = .wk σ := by rw [comp, comp_id]

/-- Upgrades a thinning to a substitution. -/
@[coe, aesop 1%, grind] def ThinE.toSubst : ThinE γ δ -> SubstE γ δ
| .nil => .nil
| .wk σ => SubstE.wk σ.toSubst
| .lift σ => SubstE.lift σ.toSubst

@[simp, grind =] theorem VarE.ren_id {γ} {v : VarE γ} : VarE.ren v (ThinE.id γ) = v := by
  match γ, v with
  | γ+1, .vz => rfl
  | γ+1, .vs v => rw [ThinE.id, VarE.ren, VarE.ren_id]

@[aesop 10%, grind =] theorem VarE.ren_wki_eq_vs {v : VarE γ} : v.ren .wki = vs v := by simp_all only [ThinE.wki, ren, ren_id]
@[aesop 10%, grind =] theorem VarE.ren_wk_eq_ren_vs_lift (v : VarE δ) (σ : ThinE γ δ) : v⌊.wk σ⌋ = (vs v)⌊σ.lift⌋ := by cases v <;> (rw [ren]; rfl)
@[aesop 50%, grind =] theorem VarE.ren_vs_lift_eq_ren_wk (v : VarE δ) (σ : ThinE γ δ) : (vs v)⌊.lift σ⌋ = v⌊.wk σ⌋ := by cases v <;> (rw [ren]; rfl)
@[aesop 50%, grind =] theorem VarE.ren_vs_lift_eq_vs_ren (v : VarE δ) (σ : ThinE γ δ) : (vs v)⌊.lift σ⌋ = .vs v⌊σ⌋ := by rfl
@[aesop 50%, grind =] theorem VarE.subst_vs_lift_eq_subst_wk (v : VarE δ) (σ : SubstE γ δ) : (vs v)[.lift σ] = v[.wk σ] := by rfl
@[aesop 10%, grind =] theorem VarE.subst_wk_eq_subst_vs_lift (v : VarE δ) (σ : SubstE γ δ) : v[.wk σ] = (vs v)[σ.lift] := by rfl

@[aesop 1%, grind =] theorem VarE.vs_eq_ren_wki : VarE.vs v = v.ren .wki := by simp_all only [ThinE.wki, ren, ren_id]
@[aesop 10%, grind =>] theorem VarE.wki_step (h : TmE.var v = t) : TmE.var (v.ren .wki) = t.ren .wki := by
  rw [<- VarE.vs_eq_ren_wki]
  subst h
  rw [TmE.ren]
  simp_all only [ThinE.wki, ren, ren_id]

@[aesop 10%, grind ->] theorem VarE.wk_step (h : TmE.var (.ren v σ) = (.ren t σ)) : TmE.var (v.ren (.wk σ)) = t.ren (.wk σ) := by
  rw [VarE.ren_wk_eq_ren_vs_lift]
  rw [ren]
  rw [<- ThinE.comp_wki]
  rw [<- TmE.ren_comp]
  rw [<- h]
  rw [VarE.vs_eq_ren_wki]
  rfl
@[aesop apply 10%, grind.] theorem TmE.ren_wki_step {x y : TmE γ} (h : x = y) : x.ren .wki = y.ren .wki := by
  subst h
  rfl

@[aesop 1%, grind =] theorem VarE.vs_ren_eq_ren_wk : VarE.vs (.ren v σ) = v.ren (.wk σ) := by simp_all only [ren]

@[aesop norm, grind =] theorem ThinE.lift_toSubst {σ : ThinE γ δ} : (ThinE.lift σ).toSubst = SubstE.lift σ.toSubst := rfl
@[aesop norm, grind =] theorem ThinE.wk_toSubst : toSubst (ThinE.wk σ) = SubstE.wk σ.toSubst := rfl
@[aesop norm, grind =] theorem ThinE.id_toSubst : toSubst (ThinE.id γ) = .id := by
  cases γ
  . rfl
  rw [id]
  rw [toSubst]
  rw [id_toSubst]
  rfl
@[aesop norm, grind =] theorem ThinE.wki_toSubst : toSubst (@ThinE.wki γ) = SubstE.wki := by simp_all only [wki, wk_toSubst, id_toSubst, SubstE.wki]
@[aesop norm, grind =] theorem ThinE.wk_id_toSubst : toSubst (ThinE.wk (.id γ)) = SubstE.wk .id := by simp_all only [wk_toSubst, id_toSubst]

@[aesop 1%, grind =, grind =_] theorem VarE.vs_ren_eq_ren_wki {γ δ}  (v : VarE δ) (σ : ThinE γ δ) : vs v⌊σ⌋ = v⌊σ⌋⌊.wki⌋ := by simp_all only [ThinE.wki, ren, ren_id]

@[aesop 1%, grind =, grind =_] theorem VarE.ren_wk_σ_eq_var_ren_wki : TmE.var v⌊ThinE.wk σ⌋ = (TmE.var v⌊σ⌋)⌊.wki⌋ := by
  rw [<- ThinE.comp_wki]
  rw [<- VarE.ren_comp]
  rw [<- TmE.ren]

@[grind =, grind =_] theorem VarE.subst_σ_ren_wki_compRen {v :VarE γ} : v[σ]⌊ThinE.wki⌋ = v[SubstE.compST σ .wki] := by
  let γ+1 := γ
  let .cons σ t := σ
  rw [SubstE.compST]
  match v with
  | .vz => rfl
  | .vs v => exact VarE.subst_σ_ren_wki_compRen (v := v) (σ := σ)

@[grind =_] theorem VarE.subst_wk_eq_subst_ren_wki {v : VarE γ} : v[.wk σ] = v[σ]⌊ThinE.wki⌋ := by rw [VarE.subst_σ_ren_wki_compRen]; rfl

@[grind ->] theorem VarE.subst_wk_eq_subst_wk_toSubst (h : TmE.var v⌊σ⌋ = v[ThinE.toSubst σ]) : TmE.var v⌊ThinE.wk σ⌋ = v[SubstE.wk (ThinE.toSubst σ)] := by
  rw [<- ThinE.comp_wki, <- VarE.ren_comp]
  rw [<- TmE.ren]
  rw [h]
  rw [VarE.subst_wk_eq_subst_ren_wki]

open ThinE (toSubst)

@[aesop norm, grind =] theorem VarE.ren_toSubst (v : VarE δ) (σ : ThinE γ δ) : .var (VarE.ren v σ) = VarE.subst v σ.toSubst := by
  match γ, δ, v, σ with
  | γ+1, δ  , v    , .wk σ   =>
    rw [toSubst]
    have ih := VarE.ren_toSubst v σ
    exact VarE.subst_wk_eq_subst_wk_toSubst ih
  | γ+1, δ+1, .vz  , .lift σ =>
    rw [toSubst]
    rw [ren]
    rw [SubstE.lift]
    rewrite [VarE.subst]
    rfl
  | γ+1, δ+1, .vs v, .lift σ =>
    have ih := VarE.ren_toSubst v σ
    rw [VarE.ren]
    rw [<- VarE.ren]
    rw [toSubst]
    rw [VarE.subst_vs_lift_eq_subst_wk]
    exact VarE.subst_wk_eq_subst_wk_toSubst ih
  | 0  , δ+1, .vz  , σ       => nomatch σ

mutual
  @[aesop norm, grind =] theorem TyE.ren_toSubst {σ : ThinE γ δ} : TyE.ren A σ = TyE.subst A σ.toSubst := by
    match A with
    | .U => rfl
    | .El t => rw [TyE.ren, TyE.subst, TmE.ren_toSubst]
    | .Pi A B => rw [TyE.ren, TyE.subst, TyE.ren_toSubst, TyE.ren_toSubst]; rfl
    | .Sum A B => rw [TyE.ren, TyE.subst, TyE.ren_toSubst, TyE.ren_toSubst]
    | .Unit => rfl

  @[aesop norm, grind =] theorem TmE.ren_toSubst {σ : ThinE γ δ} : TmE.ren t σ = TmE.subst t σ.toSubst := by
    match t with
    | .var v =>
      have h : (TmE.var v)⌊σ⌋ = (TmE.var v⌊σ⌋) := by simp_all only [TmE.ren_eq_1']
      rw [TmE.subst]
      rw [h]
      simp_all only [TmE.ren, VarE.ren_toSubst]
    | .app A B f a => simp_all only [TmE.ren, TyE.ren_toSubst, TmE.ren_toSubst, TmE.subst, ThinE.lift_toSubst, SubstE.lift, SubstE.wk]
    | .lam A B b => simp_all only [TmE.ren, TyE.ren_toSubst, TmE.ren_toSubst, TmE.subst, ThinE.lift_toSubst, SubstE.lift, SubstE.wk]
    | .pi A B => simp_all only [TmE.ren, TmE.ren_toSubst, TmE.subst, ThinE.lift_toSubst, SubstE.lift, SubstE.wk]
    | .left a => simp_all only [TmE.ren, TmE.ren_toSubst, TmE.subst]
    | .right b => simp_all only [TmE.ren, TmE.ren_toSubst, TmE.subst]
    | .elimSum A B Mot l r t => simp_all only [TmE.ren, TyE.ren_toSubst, TmE.ren_toSubst, TmE.subst, ThinE.lift_toSubst, SubstE.lift, SubstE.wk]
    | .unit => rfl
end

theorem SubstE.compRen_wki' (σ : SubstE γ δ) : SubstE.compST σ ThinE.wki = SubstE.wk σ := by grind only [wk, ThinE.wki]
@[grind =, grind =_] theorem SubstE.compRen_wki (σ : SubstE γ δ) : SubstE.compST σ (.wk (.id _)) = SubstE.wk σ := compRen_wki' σ

@[simp, grind =, grind =_] theorem SubstE.comp_wki (σ : SubstE γ δ) : comp σ (.wk .id) = .wk σ := by
  match σ with
  | .nil => rfl
  | .cons σ t =>
    have ih := comp_wki σ
    rw [comp]
    conv => rhs; rw [wk]
    rw [SubstE.compST]
    rw [TmE.ren_toSubst, ThinE.wki_toSubst, wki]
    rw [ih]
    rw [wk]

@[aesop 1%] theorem SubstE.comp_wki' (σ : SubstE γ δ) :  .wk σ = comp σ (.wk .id) := by simp_all only [comp_wki]

@[grind =, simp] theorem VarE.subst_vz_lift : VarE.vz[.lift σ] = .var .vz := by rfl

/-- `id = ⟨wk id, 0⟩` -/
@[aesop 1%, grind =] theorem SubstE.id_1 : (@SubstE.id (γ+1)) = (.wk .id ;; .var .vz) := rfl
/-- `id = ⟨wk (wk id), 1, 0⟩` -/
@[aesop 1%, grind =] theorem SubstE.id_2 : (@SubstE.id (γ+2)) = (.wk (.wk .id) ;; .var (.vs .vz) ;; .var .vz) := rfl
/-- `id = ⟨wk^3 id, 2, 1, 0⟩` -/
@[aesop 1%, grind =] theorem SubstE.id_3 : (@SubstE.id (γ+3)) = (.wk (.wk (.wk .id)) ;; .var (.vs (.vs .vz)) ;; .var (.vs .vz) ;; .var .vz) := rfl
/-- `wk id = ⟨wk (wk id), 1⟩` -/
@[aesop 1%, grind =] theorem SubstE.wk1_1 : .wk (@SubstE.id (γ+1)) = (.wk (.wk .id) ;; .var (.vs .vz)) := rfl
/-- `wk id = ⟨wk^3 id, 2, 1⟩` -/
@[aesop 1%, grind =] theorem SubstE.wk1_2 : .wk (@SubstE.id (γ+2)) = ((.wk (.wk (.wk .id))) ;; .var (.vs (.vs .vz)) ;; .var (.vs .vz)) := rfl
/-- `wk (wk id) = ⟨wk^3 id, 2⟩` -/
@[aesop 1%, grind =] theorem SubstE.wk2_1 : .wk (.wk (@SubstE.id (γ+1))) = (.wk (.wk (.wk .id)) ;; .var (.vs (.vs .vz))) := rfl
/-- `wk (wk id) = ⟨wk^4 id, 3, 2⟩` -/
@[aesop 1%, grind =] theorem SubstE.wk2_2 : .wk (.wk (@SubstE.id (γ+2))) = ((.wk (.wk (.wk (.wk .id)))) ;; .var (.vs (.vs (.vs .vz))) ;; .var (.vs (.vs .vz))) := rfl

@[aesop 10%, grind =, grind =_] theorem SubstE.compSTT_assoc {γ θ₁ θ₂ δ : Nat}
  {σ₁ : ThinE γ θ₁}
  {σ₂ : ThinE θ₁ θ₂}
  {σ₃ : SubstE θ₂ δ}
  : SubstE.compST σ₃ (σ₂ ∘ σ₁) = SubstE.compST (SubstE.compST σ₃ σ₂) σ₁
  := by
    match σ₃ with
    | .nil => simp_all only [SubstE.compST]
    | .cons σ₃ t =>
      have ih := SubstE.compSTT_assoc (σ₁ := σ₁) (σ₂ := σ₂) (σ₃ := σ₃)
      simp only [SubstE.compST]
      rw [ih]
      rw [TmE.ren_comp]

@[aesop 20%, grind =, grind =_] theorem ThinE.comp_wk_idi_lift_eq_wk : ThinE.wk (.id _) ∘ ThinE.lift σ₁ = .wk σ₁ := by simp_all only [ThinE.comp, ThinE.id_comp]
@[aesop 20%, grind =, grind =_] theorem ThinE.comp_wki_lift_eq_wk : ThinE.wki ∘ ThinE.lift σ₁ = .wk σ₁ := by simp_all only [ThinE.wki, ThinE.comp, ThinE.id_comp]

@[aesop 90%, grind =, grind =_] theorem SubstE.compST_lift {γ θ δ : Nat} (σ₂ : SubstE θ δ) (σ₁ : ThinE γ θ)
  : SubstE.compST (SubstE.lift σ₂) (.lift σ₁) = SubstE.lift (SubstE.compST σ₂ σ₁)
  := by
    rw [lift, SubstE.compST]
    conv => lhs; rw [TmE.ren, VarE.ren]
    conv => rhs; rw [lift, wk]
    grind only [= SubstE.compSTT_assoc, =_ compRen_wki, =_ ThinE.comp_wk_id, = compRen_wki,
      =_ ThinE.comp_wki_lift_eq_wk, = ThinE.comp_wki_lift_eq_wk, =_ ThinE.comp_wki, = ThinE.comp_wki,
      =_ comp_wki, wk, ThinE.wki, =_ SubstE.compSTT_assoc]

@[aesop norm, grind =, grind =_] theorem VarE.subst_ren_comp {γ θ δ : Nat} (v : VarE δ) (σ₂ : SubstE θ δ) (σ₁ : ThinE γ θ) : TmE.ren (VarE.subst v σ₂) σ₁ = VarE.subst v (SubstE.compST σ₂ σ₁) := by
  match v, σ₂ with
  | .vz, .cons σ₂ t => rfl
  | .vs v, .cons σ₂ t =>
    rw [VarE.subst]
    have ih := subst_ren_comp v σ₂ σ₁
    simp_all only [TmE.ren_toSubst, subst_comp, SubstE.compST, subst]

mutual
  @[aesop norm, grind =, grind =_] theorem TyE.subst_ren_comp {γ θ δ : Nat} (A : TyE δ) (σ₂ : SubstE θ δ) (σ₁ : ThinE γ θ) : TyE.ren (TyE.subst A σ₂) σ₁ = TyE.subst A (SubstE.compST σ₂ σ₁) := by
    match A with
    | .U => rw [TyE.subst, TyE.subst, TyE.ren]
    | .El t =>
      rw [TyE.subst, TyE.subst, TyE.ren, TmE.subst_ren_comp]
      done
    | .Pi A B =>
      rw [TyE.subst, TyE.subst, TyE.ren]
      /- ih_A : `A[δ][σ] = A[δ ∘ σ]` -/
      have ih_A : TyE.ren (TyE.subst A σ₂) σ₁ = TyE.subst A (SubstE.compST σ₂ σ₁) := TyE.subst_ren_comp .. --(A := A) σ₂ σ₁
      rw [ih_A]
      rw [TyE.subst_ren_comp] -- ih_B : `B[lift δ][lift σ] = B[lift δ ∘ lift σ]`
      simp_all only [TyE.Pi.injEq, true_and]
      grind only [= SubstE.compST_lift, SubstE.lift, = TyE.ren_toSubst]
    | .Sum A B =>
      rw [TyE.subst, TyE.ren]
      rw [TyE.subst_ren_comp]
      rw [TyE.subst_ren_comp]
      rfl
    | .Unit => rfl
  termination_by sizeOf A

  @[aesop norm, grind =, grind =_] theorem TmE.subst_ren_comp {γ θ δ} (t : TmE δ) (σ₂ : SubstE θ δ) (σ₁ : ThinE γ θ) : TmE.ren (TmE.subst t σ₂) σ₁ = TmE.subst t (SubstE.compST σ₂ σ₁) := by
    match t with
    | .var v =>
      dsimp [TmE.subst, TmE.subst]
      rw [VarE.subst_ren_comp]
    | .app A B f a =>
      dsimp [TmE.subst]
      rw [TmE.subst_ren_comp]
      rw [TmE.subst_ren_comp]
      rw [TyE.subst_ren_comp]
      rw [TyE.subst_ren_comp]
      grind only [= SubstE.compST_lift, SubstE.lift]
    | .lam A B body =>
      dsimp [TmE.subst]
      rw [TmE.subst_ren_comp]
      rw [TyE.subst_ren_comp]
      rw [TyE.subst_ren_comp]
      grind only [= SubstE.compST_lift, SubstE.lift]
    | .pi A B =>
      dsimp [TmE.subst]
      rw [TmE.subst_ren_comp]
      rw [TmE.subst_ren_comp]
      grind only [= SubstE.compST_lift, SubstE.lift]
    | .left a =>
      dsimp [TmE.subst]
      rw [TmE.subst_ren_comp]
    | .right b =>
      dsimp [TmE.subst]
      rw [TmE.subst_ren_comp]
    | .elimSum A B Mot l r t =>
      dsimp [TmE.subst]
      rw [TmE.subst_ren_comp]
      rw [TmE.subst_ren_comp]
      rw [TmE.subst_ren_comp]
      rw [TyE.subst_ren_comp]
      rw [TyE.subst_ren_comp]
      rw [TyE.subst_ren_comp]
      grind only [= SubstE.compST_lift, SubstE.lift]
    | .unit => rfl
  termination_by sizeOf t
end

@[grind =, grind =_, aesop 50%] theorem SubstE.compST_wki_lift (σ : ThinE γ δ) : SubstE.compST .wki (.lift σ) = .wk σ.toSubst := by
  match σ with
  | .nil => rfl
  | .wk σ =>
    have ih := SubstE.compST_wki_lift σ
    grind only [= TmE.ren_comp, = SubstE.compST_lift, = SubstE.compSTT_assoc, = ThinE.comp_id,
      = ThinE.comp_wk_id, = id_1, = TmE.ren_toSubst, TmE.subst, =_ compRen_wki, lift,
      =_ ThinE.comp_wk_id, = compRen_wki, =_ ThinE.comp_wki_lift_eq_wk, id, = wk1_1, wki,
      = ThinE.comp_wki_lift_eq_wk, SubstE.compST, = ThinE.id_comp, ThinE.id, =_ ThinE.comp_wki, toSubst,
      = VarE.subst_ren_comp, comp, = ThinE.comp_assoc, = ThinE.comp_wki, =_ comp_wki, wk, ThinE.wki,
      =_ SubstE.compSTT_assoc]
  | .lift σ =>
    have ih := SubstE.compST_wki_lift σ
    rw [wki, wk, ThinE.wki, wk, ThinE.wki] at ih
    rw [wki, wk1_1, SubstE.compST, TmE.ren, VarE.ren, VarE.ren, wk, wk, wk, ThinE.wki, ThinE.wki]
    rw [ThinE.wki]
    simp only [toSubst, lift, wk, ThinE.wki, SubstE.compST]
    grind only [= SubstE.compSTT_assoc, = id_1, = ThinE.comp_id, = ThinE.comp_wk_id, = TmE.ren_toSubst,
      =_ compRen_wki, TmE.subst, lift, =_ ThinE.comp_wk_id, = compRen_wki, = ThinE.id_toSubst,
      =_ ThinE.comp_wki_lift_eq_wk, = wk1_1, id, SubstE.compST, = ThinE.comp_wki_lift_eq_wk,
      = ThinE.id_comp, ThinE.id, =_ ThinE.comp_wki, toSubst, comp, = ThinE.comp_wki, =_ comp_wki,
      = ThinE.comp_assoc, wk, ThinE.wki, =_ SubstE.compSTT_assoc]

@[grind =, grind =_, aesop 50%] theorem SubstE.compST_wk_id_lift (σ : ThinE γ δ) : SubstE.compST (.wk .id) (.lift σ) = .wk σ.toSubst := by
  grind only [=_ compST_wki_lift,
    =_ compRen_wki, =_ ThinE.comp_wk_id, =_ compSTT_assoc, =_ ThinE.comp_wki_lift_eq_wk, wki,
    =_ ThinE.comp_wk_idi_lift_eq_wk, =_ ThinE.comp_wki, =_ comp_wki, wk, ThinE.wki]

@[grind =] theorem SubstE.id_compST : SubstE.compST .id σ = σ.toSubst := by
  cases σ
  . rfl
  . grind only [=_ compST_wki_lift, = ThinE.comp_id, ThinE.comp, =_ compRen_wki,
    =_ ThinE.comp_wk_id, = compRen_wki, =_ ThinE.comp_wki_lift_eq_wk, = compSTT_assoc, wki,
    = ThinE.id_comp, =_ ThinE.comp_wk_idi_lift_eq_wk, = ThinE.id_refold, =_ ThinE.comp_assoc,
    =_ ThinE.comp_wki, toSubst, = ThinE.comp_assoc, =_ comp_wki, wk, = ThinE.wk_toSubst,
    =_ compST_wk_id_lift, ThinE.wki]
  . grind only [=_ compST_wki_lift, = compST_wk_id_lift, = id_1, = TmE.ren_toSubst, TmE.ren,
    = compST_lift, =_ compRen_wki, =_ ThinE.comp_wk_id, lift, =_ compSTT_assoc,
    =_ ThinE.comp_wki_lift_eq_wk, id, =_ ThinE.comp_wk_idi_lift_eq_wk, =_ ThinE.comp_wki, compST,
    =_ comp_wki, = ThinE.lift_toSubst, wk, toSubst, ThinE.wki]

mutual
  @[simp, grind =] theorem TyE.ren_id (A : TyE δ) : A.ren (.id _) = A := by
    match A with
    | .U => rfl
    | .Unit => rfl
    | .El t =>
      have ih := TmE.ren_id t
      grind only [= TmE.ren_comp, TyE.ren, = TmE.ren_toSubst, = TyE.ren_toSubst]
    | .Pi A B =>
      have ihA := TyE.ren_id A
      have ihB := TyE.ren_id B
      grind only [= TyE.ren_toSubst, ThinE.id, TyE.ren, = TyE.ren_comp]
    | .Sum A B =>
      have ihA := TyE.ren_id A
      have ihB := TyE.ren_id B
      grind

  @[simp, grind =] theorem TmE.ren_id (t : TmE δ) : t.ren (.id _) = t := by
    match t with
    | .var v => grind only [= TmE.ren_toSubst, TmE.subst, TmE.ren, = ThinE.id_toSubst,
      → VarE.wk_step, = VarE.ren_id, → VarE.subst_wk_eq_subst_wk_toSubst, = VarE.ren_toSubst]
    | .lam A B b =>
      have ihA := TyE.ren_id A
      have ihB := TyE.ren_id B
      have ihb := TmE.ren_id b
      grind only [= TmE.ren_comp, = TmE.ren_toSubst, TmE.ren, = TyE.ren_toSubst, ThinE.id,
        = TyE.ren_comp]
    | .pi a b =>
      have := TmE.ren_id a
      have := TmE.ren_id b
      grind only [= TmE.ren_comp, = TmE.ren_toSubst, ThinE.id, TmE.ren]
    | .right r =>
      have := TmE.ren_id r
      grind only [= TmE.ren_comp, = TmE.ren_toSubst, TmE.ren]
    | .left l =>
      have := TmE.ren_id l
      grind only [= TmE.ren_comp, = TmE.ren_toSubst, TmE.ren]
    | .elimSum M A B l r t =>
      have := TyE.ren_id A
      have := TyE.ren_id B
      have := TyE.ren_id M
      have := TmE.ren_id l
      have := TmE.ren_id r
      have := TmE.ren_id t
      grind only [= TmE.ren_comp, = TmE.ren_toSubst, = TyE.ren_toSubst, ThinE.id, = TyE.ren_comp, TmE.ren]
    | .app A B f a =>
      have ihA := TyE.ren_id A
      have ihB := TyE.ren_id B
      have ihf := TmE.ren_id f
      have iha := TmE.ren_id a
      grind only [TmE.ren, = TmE.ren_comp, = TmE.ren_toSubst, = TyE.ren_toSubst, ThinE.id,
        = TyE.ren_comp]
    | .unit => rfl
    done
end

@[simp, grind =] theorem SubstE.compST_id : SubstE.compST σ (.id _) = σ := by
  match σ with
  | .nil => rfl
  | .cons σ t =>
    have ih := SubstE.compST_id (σ := σ)
    -- grind?
    rw [SubstE.compST]
    rw [ih]
    congr 1
    rw [TmE.ren_id]

@[grind =] theorem SubstE.id_refold : SubstE.lift (.id (γ := γ)) = .id := rfl
@[grind =] theorem SubstE.id_refold' : SubstE.cons (.wk .id (γ := γ)) (.var .vz) = .id := rfl

@[aesop 50%, grind =, grind =_] theorem SubstE.compSST_assoc {γ θ₁ θ₂ δ : Nat}
  {σ₁ : ThinE γ θ₁} {σ₂ : SubstE θ₁ θ₂} {σ₃ : SubstE θ₂ δ}
  : σ₃ ∘ (σ₂ ∘ᵀ σ₁) = (σ₃ ∘ σ₂) ∘ᵀ σ₁ := by
    match σ₃ with
    | .nil => rfl
    | .cons σ₃ t =>
      rw [SubstE.comp]
      rw [SubstE.comp]
      rw [SubstE.compST]
      rw [SubstE.compSST_assoc]
      grind only [= TmE.ren_toSubst, =_ TmE.subst_ren_comp]

/-- Composition of a thinning with a substitution. -/
@[grind, aesop 10%] def SubstE.compTS : ThinE θ δ → SubstE γ θ → SubstE γ δ
| .nil      , σ₂ => .nil
| .wk   σ₁  , .cons σ₂ t => compTS σ₁ σ₂
| .lift σ₁  , .cons σ₂ t => (compTS σ₁ σ₂) ;; t

namespace Erased.Notation
  scoped infixl:67 (name := stxCompRenSubst) " ᵀ∘ " => SubstE.compTS
end Erased.Notation

@[grind =, simp] theorem SubstE.compTS_wki_cons : (ThinE.wk (.id δ)) ᵀ∘ (σ ;; t) = σ := by
  match σ with
  | .nil => rfl
  | .cons σ t =>
    have ih := compTS_wki_cons (σ := σ) (t := t)
    rw [ThinE.id]
    rw [compTS]
    rw [compTS]
    grind

@[simp, grind =] theorem SubstE.compTS_wk_id_cons (σ : SubstE γ δ) : SubstE.compTS (.wk (.id _)) (σ ;; t) = σ := compTS_wki_cons

@[aesop 10%, grind =, grind =_] theorem SubstE.compTSS_assoc {γ θ₁ θ₂ δ : Nat}
  {σ₁ : SubstE γ θ₁} {σ₂ : SubstE θ₁ θ₂} {σ₃ : ThinE θ₂ δ}
  : σ₃ ᵀ∘ (σ₂ ∘ σ₁) = (σ₃ ᵀ∘ σ₂) ∘ σ₁
  := by
    match σ₃, σ₂ with
    | .nil     , _=> rfl
    | .wk σ₃   , .cons σ₂ t =>
      have ih := @SubstE.compTSS_assoc _ _ _ _ σ₁ σ₂ σ₃
      grind only [compTS, ThinE.comp, =_ ThinE.comp_wk_id, =_ ThinE.comp_wki_lift_eq_wk,
        =_ ThinE.comp_wki, comp, ThinE.wki]
    | .lift σ₃ , .cons σ₂ t =>
      have ih := @SubstE.compTSS_assoc _ _ _ _ σ₁ σ₂ σ₃
      grind only [comp, compTS]

@[aesop 10%, grind =, grind =_] theorem SubstE.compTTS_assoc {γ θ₁ θ₂ δ : Nat}
  {σ₁ : SubstE γ θ₁} {σ₂ : ThinE θ₁ θ₂} {σ₃ : ThinE θ₂ δ}
  : σ₃ ᵀ∘ (σ₂ ᵀ∘ σ₁) = (σ₃ ∘ σ₂) ᵀ∘ σ₁
  := by
    match σ₃, σ₂, σ₁ with
    | .nil    , .nil    , .nil => rfl
    | .nil    , .nil    , _ => grind only [ThinE.comp, compTS]
    | σ₃      , .wk   σ₂, .cons σ₁ t =>
      have ih := @compTTS_assoc _ _ _ _ σ₁ σ₂ σ₃
      grind only [compTS, ThinE.comp, =_ ThinE.comp_wk_id, =_ ThinE.comp_wki_lift_eq_wk,
        =_ ThinE.comp_wk_idi_lift_eq_wk, =_ ThinE.comp_wki, = ThinE.comp_assoc, ThinE.wki]
    | .wk   σ₃, .lift σ₂, .cons σ₁ t =>
      have ih := @compTTS_assoc _ _ _ _ σ₁ σ₂ σ₃
      grind only [compTS, ThinE.comp, =_ ThinE.comp_wk_id, =_ ThinE.comp_wki_lift_eq_wk,
        =_ ThinE.comp_wk_idi_lift_eq_wk, =_ ThinE.comp_assoc, =_ ThinE.comp_wki, ThinE.wki]
    | .lift σ₃, .lift σ₂, .cons σ₁ t =>
      have ih := @compTTS_assoc _ _ _ _ σ₁ σ₂ σ₃
      grind only [ThinE.comp, compTS]
    | .nil    , .lift σ₂, .cons σ₁ t => grind only [ThinE.comp, compTS]

@[aesop 10%, grind =, grind =_] theorem SubstE.compST_toSubst (σ₂ : SubstE θ δ) (σ₁ : ThinE γ θ) : σ₂ ∘ σ₁.toSubst = σ₂ ∘ᵀ σ₁ := by
  match σ₂ with
  | .nil => rfl
  | .cons σ₂ t =>
    have ih := compST_toSubst σ₂ σ₁
    grind only [= TmE.ren_toSubst, compST, comp]

@[grind =, simp] theorem SubstE.comp_nil {σ : SubstE _ _} : σ ∘ (@SubstE.nil γ) = SubstE.nil := by
  cases σ
  rfl

@[grind =, simp] theorem ThinE.comp_nil {σ : ThinE _ _} : σ ∘ (@ThinE.nil δ) = .nil := by
  cases σ
  grind only [comp]

@[aesop norm, grind =, grind =_] theorem VarE.thin_subst_comp {γ θ δ : Nat} (v : VarE δ) (σ₂ : ThinE θ δ) (σ₁ : SubstE γ θ) : VarE.subst (VarE.ren v σ₂) σ₁ = VarE.subst v (SubstE.compTS σ₂ σ₁) := by
  match v, σ₂, σ₁ with
  | .vz, .lift σ₂, .cons σ₁ t => rfl
  | .vs v, .lift σ₂, .cons σ₁ t =>
    have ih := thin_subst_comp v σ₂ σ₁
    grind only [=_ ThinE.comp_wk_id, = ren_vs_lift_eq_ren_wk, =_ ThinE.comp_wki_lift_eq_wk,
      = vs_eq_ren_wki, = vs_ren_eq_ren_wk, = ren_wk_eq_ren_vs_lift, =_ ThinE.comp_wk_idi_lift_eq_wk,
      ren, =_ ThinE.comp_wki, subst, SubstE.compTS, = ren_wki_eq_vs, = ren_vs_lift_eq_vs_ren,
      = ren_comp, ThinE.wki, = vs_ren_eq_ren_wki]
  | v, .wk   σ₂, .cons σ₁ t =>
    have ih := thin_subst_comp v σ₂ σ₁
    grind only [SubstE.compTS, ThinE.comp, = ren_vs_lift_eq_ren_wk, =_ ThinE.comp_wk_id,
      =_ ThinE.comp_wki_lift_eq_wk, = vs_eq_ren_wki, =_ SubstE.compTTS_assoc, = vs_ren_eq_ren_wk,
      = ren_wk_eq_ren_vs_lift, ren, =_ ThinE.comp_wk_idi_lift_eq_wk, =_ ThinE.comp_wki, subst,
      = ren_vs_lift_eq_vs_ren, ThinE.wki, = vs_ren_eq_ren_wki]

mutual
  @[aesop norm, grind =, grind =_] theorem TyE.thin_subst_comp {γ θ δ : Nat} (A : TyE δ) (σ₂ : ThinE θ δ) (σ₁ : SubstE γ θ) : TyE.subst (TyE.ren A σ₂) σ₁ = TyE.subst A (SubstE.compTS σ₂ σ₁) := by
    match A with
    | .U => grind only [TyE.ren, = TyE.ren_toSubst, TyE.subst]
    | .El t =>
      simp only [TyE.ren, TyE.subst]
      rw [TmE.thin_subst_comp t σ₂ σ₁]
    | .Pi A B =>
      simp only [TyE.ren, TyE.subst]
      rw [TyE.thin_subst_comp A σ₂ σ₁]
      rw [TyE.thin_subst_comp B (σ₂.lift) (σ₁.lift)]
      grind only [= SubstE.compTSS_assoc, =_ SubstE.compRen_wki, =_ ThinE.comp_wk_id, SubstE.lift,
        =_ SubstE.compST_toSubst, =_ ThinE.comp_wki_lift_eq_wk, =_ ThinE.comp_wk_idi_lift_eq_wk,
        =_ ThinE.comp_wki, SubstE.compTS, =_ SubstE.comp_wki, SubstE.wk, ThinE.wki]
    | .Sum A B =>
      simp only [TyE.ren, TyE.subst]
      rw [TyE.thin_subst_comp A σ₂ σ₁]
      rw [TyE.thin_subst_comp B σ₂ σ₁]
    | .Unit => rfl
  termination_by sizeOf A

  @[aesop norm, grind =, grind =_] theorem TmE.thin_subst_comp {γ θ δ} (t : TmE δ) (σ₂ : ThinE θ δ) (σ₁ : SubstE γ θ) : TmE.subst (TmE.ren t σ₂) σ₁ = TmE.subst t (SubstE.compTS σ₂ σ₁) := by
    match t with
    | .var v =>
      dsimp [TmE.subst, TmE.ren]
      rw [VarE.thin_subst_comp]
    | .app A B f a =>
      dsimp [TmE.subst, TmE.ren]
      rw [TyE.thin_subst_comp]
      rw [TyE.thin_subst_comp]
      rw [TmE.thin_subst_comp]
      rw [TmE.thin_subst_comp]
      grind only [= SubstE.compTSS_assoc, =_ SubstE.compRen_wki, =_ ThinE.comp_wk_id, SubstE.lift,
        =_ SubstE.compST_toSubst, =_ ThinE.comp_wki_lift_eq_wk, =_ ThinE.comp_wk_idi_lift_eq_wk,
        =_ ThinE.comp_wki, SubstE.compTS, =_ SubstE.comp_wki, SubstE.wk, ThinE.wki]
    | .lam A B body =>
      dsimp [TmE.subst]
      rw [TmE.thin_subst_comp]
      rw [TyE.thin_subst_comp]
      rw [TyE.thin_subst_comp]
      grind only [= SubstE.compTSS_assoc, =_ SubstE.compRen_wki, =_ ThinE.comp_wk_id, SubstE.lift,
        =_ SubstE.compST_toSubst, =_ ThinE.comp_wki_lift_eq_wk, =_ ThinE.comp_wk_idi_lift_eq_wk,
        =_ ThinE.comp_wki, SubstE.compTS, =_ SubstE.comp_wki, SubstE.wk, ThinE.wki]
    | .pi A B =>
      dsimp [TmE.subst]
      rw [TmE.thin_subst_comp]
      rw [TmE.thin_subst_comp]
      grind only [= SubstE.compTSS_assoc, =_ SubstE.compRen_wki, =_ ThinE.comp_wk_id, SubstE.lift,
        =_ SubstE.compST_toSubst, =_ ThinE.comp_wki_lift_eq_wk, =_ ThinE.comp_wk_idi_lift_eq_wk,
        =_ ThinE.comp_wki, SubstE.compTS, =_ SubstE.comp_wki, SubstE.wk, ThinE.wki]
    | .left a =>
      dsimp [TmE.subst]
      rw [TmE.thin_subst_comp]
    | .right b =>
      dsimp [TmE.subst]
      rw [TmE.thin_subst_comp]
    | .elimSum A B Mot l r t =>
      dsimp [TmE.subst]
      rw [TmE.thin_subst_comp]
      rw [TmE.thin_subst_comp]
      rw [TmE.thin_subst_comp]
      rw [TyE.thin_subst_comp]
      rw [TyE.thin_subst_comp]
      rw [TyE.thin_subst_comp]
      grind only [= SubstE.compTSS_assoc, =_ SubstE.compRen_wki, =_ ThinE.comp_wk_id, SubstE.lift,
        =_ SubstE.compST_toSubst, =_ ThinE.comp_wki_lift_eq_wk, =_ ThinE.comp_wk_idi_lift_eq_wk,
        =_ ThinE.comp_wki, SubstE.compTS, =_ SubstE.comp_wki, SubstE.wk, ThinE.wki]
    | .unit => rfl
  termination_by sizeOf t
end

@[aesop 10%, grind =, grind =_] theorem SubstE.compSTS_assoc {γ θ₁ θ₂ δ : Nat}
  {σ₁ : SubstE γ θ₁} {σ₂ : ThinE θ₁ θ₂} {σ₃ : SubstE θ₂ δ}
  : σ₃ ∘ (σ₂ ᵀ∘ σ₁) = (σ₃ ∘ᵀ σ₂) ∘ σ₁
  := by
    match σ₃, σ₂, σ₁ with
    | .nil      , _, _ => rfl
    | .cons σ₃ t, .nil, .cons σ₁ u =>
      have ih := @compSTS_assoc _ _ _ _ (.cons σ₁ u) .nil σ₃
      grind only [= TmE.ren_toSubst, toSubst, =_ compST_toSubst, compST, comp,
        =_ TmE.thin_subst_comp, compTS]
    | .cons σ₃ t, .nil, .nil =>
      have ih := @compSTS_assoc γ _ _ _ .nil .nil σ₃
      rw [comp]
      rw [compST]
      rw [comp]
      rw [compTS]
      grind only [= TmE.thin_subst_comp, = TmE.ren_toSubst, =_ compST_toSubst, compTS]
    | .cons σ₃ t, .wk σ₂, .cons σ₁ u =>
      have ih := @compSTS_assoc _ _ _ _ σ₁ σ₂ σ₃
      have : (σ₃ ;; t) ∘ (ThinE.wk σ₂ ᵀ∘ (σ₁ ;; u)) = (σ₃ ∘ (σ₂ ᵀ∘ σ₁)) ;; (t[ThinE.wk σ₂ ᵀ∘ (σ₁ ;; u)]) := by
        grind only [compTS, =_ ThinE.comp_wk_id, =_ compST_toSubst, =_ ThinE.comp_wki_lift_eq_wk,
          =_ ThinE.comp_wk_idi_lift_eq_wk, =_ ThinE.comp_wki, comp, =_ TmE.thin_subst_comp]
      rw [ih] at this
      rw [this]
      clear this
      have : ((σ₃ ;; t) ∘ᵀ ThinE.wk σ₂) ∘ (σ₁ ;; u) = (((σ₃ ∘ᵀ σ₂) ∘ᵀ ThinE.wki) ∘ (σ₁ ;; u)) ;; (t.ren (.wk σ₂) |>.subst (σ₁ ;; u)) := by
        grind only [compTS, = ThinE.wk_id_toSubst, ThinE.comp, = TmE.ren_toSubst,
          =_ ThinE.comp_wk_id, = compRen_wki, =_ compST_toSubst, =_ compSTT_assoc,
          =_ ThinE.comp_wki_lift_eq_wk, =_ compTTS_assoc, = compSTT_assoc, = ThinE.wki_toSubst,
          =_ ThinE.comp_wk_idi_lift_eq_wk, =_ ThinE.comp_wki, toSubst, compST, =_ compSST_assoc,
          comp, = ThinE.wk_toSubst, =_ TmE.thin_subst_comp, ThinE.wki]
      rw [this]
      clear this
      congr 1
      . -- now just need  `(σ₃ ∘ᵀ σ₂) ∘ σ₁ = ((σ₃ ∘ᵀ σ₂) ∘ᵀ ThinE.wki) ∘ (σ₁ ;; u)`
        conv => rhs; rw [<- compSTS_assoc]
        grind only [compTS, = compTS_wk_id_cons, =_ ThinE.comp_wk_id, =_ compST_toSubst,
          =_ ThinE.comp_wki_lift_eq_wk, =_ ThinE.comp_wk_idi_lift_eq_wk, =_ ThinE.comp_wki,
          = compTS_wki_cons, ThinE.wki]
      . grind only [compTS, = TmE.ren_toSubst, =_ ThinE.comp_wk_id, =_ compST_toSubst,
        =_ ThinE.comp_wki_lift_eq_wk, =_ ThinE.comp_wk_idi_lift_eq_wk, =_ ThinE.comp_wki,
        =_ TmE.thin_subst_comp]
    | .cons σ₃ t, .lift σ₂, .cons σ₁ u =>
      have ih := @compSTS_assoc _ _ _ _ (.cons σ₁ u) (.lift σ₂) σ₃
      grind only [= TmE.ren_toSubst, =_ compST_toSubst, compST, comp, compTS, = ThinE.lift_toSubst,
        =_ TmE.thin_subst_comp, toSubst]

@[grind =, grind =_] theorem SubstE.comp_toSubst_wk_id {σ : ThinE γ δ} : toSubst σ ∘ᵀ .wk (.id γ) = (σ ∘ ThinE.wk (ThinE.id γ)).toSubst := by
  grind only [= SubstE.compSTT_assoc, = ThinE.comp_id, = ThinE.comp_wk_id, ThinE.comp, =_ ThinE.comp_wk_id,
    = compRen_wki, =_ ThinE.comp_wki_lift_eq_wk, = ThinE.id_comp, = ThinE.id_refold,
    =_ SubstE.compST_wki_lift, =_ ThinE.comp_wki, toSubst, =_ comp_wki, = ThinE.comp_assoc, wk,
    = ThinE.wk_toSubst, ThinE.wki]

@[aesop 10%, grind =, grind =_] theorem ThinE.comp_toSubst (σ₂ : ThinE θ δ) (σ₁ : ThinE γ θ) : (σ₂ ∘ σ₁).toSubst = σ₂.toSubst ∘ σ₁.toSubst := by
  match σ₂, σ₁ with
  | σ₂      , .wk σ₁   =>
    have ih := comp_toSubst σ₂ σ₁
    grind only [=_ SubstE.compST_wki_lift, = comp_id, = comp_wk_id, comp, =_ SubstE.compRen_wki,
      =_ comp_wk_id, =_ comp_wki_lift_eq_wk, = SubstE.compSTT_assoc, SubstE.wki,
      =_ SubstE.comp_toSubst_wk_id, = id_comp, =_ comp_wk_idi_lift_eq_wk, = SubstE.compSST_assoc,
      = id_refold, =_ comp_assoc, =_ comp_wki, toSubst, = comp_wki, =_ SubstE.comp_wki,
      = comp_assoc, SubstE.wk, = wk_toSubst, =_ SubstE.compST_wk_id_lift, wki]
  | .nil    , .nil     => grind only [toSubst, comp, = comp_assoc, SubstE.comp]
  | .nil    , .lift σ₁ => rfl
  | .wk σ₂  , .lift σ₁ =>
    have ih := comp_toSubst σ₂ σ₁
    grind only [=_ SubstE.compST_wki_lift, = comp_id, comp, =_ SubstE.compRen_wki,
      = SubstE.compST_toSubst, SubstE.lift, =_ comp_wk_id, =_ SubstE.compST_toSubst,
      =_ SubstE.compSTT_assoc, =_ comp_wki_lift_eq_wk, = comp_wk_idi_lift_eq_wk,
      = SubstE.compSTT_assoc, SubstE.wki, =_ SubstE.comp_toSubst_wk_id, = comp_wki_lift_eq_wk,
      = id_comp, =_ comp_wk_idi_lift_eq_wk, = id_refold, =_ comp_assoc, =_ comp_wki, toSubst,
      =_ SubstE.compSST_assoc, = comp_assoc, =_ SubstE.comp_wki, = lift_toSubst, SubstE.wk,
      = wk_toSubst, =_ SubstE.compST_wk_id_lift, wki]
  | .lift σ₂, .lift σ₁ =>
    have ih := comp_toSubst σ₂ σ₁
    grind only [= SubstE.compST_lift, = SubstE.compST_toSubst, SubstE.lift, comp, = lift_toSubst,
      toSubst]

@[aesop 10%, grind =] theorem SubstE.compTS_toSubst (σ₂ : ThinE θ δ) (σ₁ : SubstE γ θ) : σ₂.toSubst ∘ σ₁ = σ₂ ᵀ∘ σ₁ := by
  match σ₂, σ₁ with
  | .nil, _ => rfl
  | .lift σ₂, .cons σ₁ t =>
    have ih := compTS_toSubst σ₂ σ₁
    grind only [compTS, = ThinE.wk_id_toSubst, =_ compST_wki_lift, = ThinE.comp_wk_id,
      =_ compSTS_assoc, ThinE.comp, = ThinE.comp_toSubst, TmE.subst, =_ compRen_wki,
      = compTS_wk_id_cons, =_ ThinE.comp_wk_id, lift, =_ ThinE.comp_toSubst, =_ compST_toSubst,
      =_ compSTT_assoc, = comp_toSubst_wk_id, =_ ThinE.comp_wki_lift_eq_wk, =_ compTTS_assoc,
      = compSTT_assoc, =_ comp_toSubst_wk_id, = ThinE.wki_toSubst, wki, = ThinE.id_comp,
      =_ ThinE.comp_wk_idi_lift_eq_wk, = ThinE.id_refold, = compSST_assoc, =_ ThinE.comp_assoc,
      =_ ThinE.comp_wki, toSubst, = id_compST, comp, =_ compSST_assoc, = ThinE.comp_assoc,
      = ThinE.comp_wki, =_ comp_wki, VarE.subst, = ThinE.lift_toSubst, = compTS_wki_cons,
      = ThinE.wk_toSubst, wk, =_ compST_wk_id_lift, ThinE.wki]
  | .wk σ₂, .cons σ₁ t =>
    have ih := compTS_toSubst σ₂ σ₁
    grind only [compTS, = ThinE.wk_id_toSubst, =_ compST_wki_lift, =_ compSTS_assoc,
      = ThinE.comp_id, ThinE.comp, = ThinE.comp_toSubst, = compST_toSubst, =_ compRen_wki,
      = compTS_wk_id_cons, =_ ThinE.comp_wk_id, =_ compST_toSubst, =_ ThinE.comp_wki_lift_eq_wk,
      = compSTT_assoc, =_ compTTS_assoc, wki, = ThinE.wki_toSubst, =_ comp_toSubst_wk_id,
      = ThinE.id_comp, =_ ThinE.comp_wk_idi_lift_eq_wk, = ThinE.id_refold, =_ ThinE.comp_assoc,
      =_ ThinE.comp_wki, toSubst, = ThinE.comp_assoc, =_ comp_wki, = ThinE.lift_toSubst,
      = compTS_wki_cons, wk, = ThinE.wk_toSubst, =_ compST_wk_id_lift, ThinE.wki]

@[grind =, simp] theorem SubstE.comp_wki_cons : SubstE.wk .id ∘ (σ ;; t) = σ := by
  grind only [compTS, = ThinE.wk_id_toSubst, =_ compSTS_assoc, ThinE.comp, = ThinE.comp_toSubst,
    =_ compRen_wki, =_ ThinE.comp_wk_id, = compRen_wki, =_ compST_toSubst,
    =_ ThinE.comp_wki_lift_eq_wk, = compSTT_assoc, =_ compTTS_assoc, =_ comp_toSubst_wk_id,
    = ThinE.wki_toSubst, = ThinE.id_comp, =_ ThinE.comp_wk_idi_lift_eq_wk, = ThinE.id_refold,
    = compSST_assoc, =_ ThinE.comp_assoc, =_ ThinE.comp_wki, toSubst, = id_compST,
    = ThinE.comp_assoc, =_ comp_wki, = ThinE.wk_toSubst, = compTS_wki_cons, wk, = compTS_toSubst,
    ThinE.wki]

@[grind =] theorem SubstE.comp_wki_lift : SubstE.wki ∘ (.lift σ) = .wk σ := by
  grind only [=_ compRen_wki, =_ ThinE.comp_wk_id, lift, =_ ThinE.comp_wki_lift_eq_wk, wki,
    =_ ThinE.comp_wki, = comp_wki_cons, =_ comp_wki, wk, ThinE.wki]


@[grind =, grind =_] theorem VarE.subst_wki_lift_eq_wk (v : VarE δ) : v[.wki][.lift σ] = v[σ][.wk .id] := by
  grind only [=_ SubstE.compRen_wki, =_ ThinE.comp_wk_id, SubstE.lift, =_ SubstE.compST_toSubst,
    = subst_comp, =_ ThinE.comp_wki_lift_eq_wk, = SubstE.comp_wki_lift, SubstE.wki,
    =_ ThinE.comp_wk_idi_lift_eq_wk, = SubstE.compSST_assoc, =_ ThinE.comp_wki, = SubstE.id_compST,
    =_ TmE.subst_ren_comp, = SubstE.comp_wki_cons, =_ SubstE.comp_wki, SubstE.wk, ThinE.wki,
    = subst_wk_eq_subst_vs_lift]

@[aesop 90%] theorem SubstE.comp_wk_lift {γ θ δ : Nat} (σ₂ : SubstE θ δ) (σ₁ : SubstE γ θ)
  : SubstE.wk σ₂ ∘ SubstE.lift σ₁ = SubstE.wk (σ₂ ∘ σ₁)
  := by
    grind only [compTS, = ThinE.wk_id_toSubst, =_ compSTS_assoc, ThinE.comp, = ThinE.comp_toSubst,
      =_ compRen_wki, =_ ThinE.comp_wk_id, lift, =_ compST_toSubst, =_ ThinE.comp_wki_lift_eq_wk,
      = compSTT_assoc, =_ compTTS_assoc, =_ comp_toSubst_wk_id, = ThinE.wki_toSubst,
      = ThinE.id_comp, =_ ThinE.comp_wk_idi_lift_eq_wk, = ThinE.id_refold, = compSST_assoc,
      =_ ThinE.comp_assoc, =_ ThinE.comp_wki, toSubst, = id_compST, =_ compSST_assoc,
      = ThinE.comp_assoc, =_ comp_wki, = ThinE.wk_toSubst, = compTS_wki_cons, wk, ThinE.wki]

 @[aesop 90%] theorem SubstE.comp_lift {γ θ δ : Nat} (σ₂ : SubstE θ δ) (σ₁ : SubstE γ θ)
  : SubstE.lift σ₂ ∘ SubstE.lift σ₁ = SubstE.lift (σ₂ ∘ σ₁)
  := by
    match σ₂ with
    | .nil => rfl
    | .cons σ₂ t =>
      have ih := comp_lift σ₂ σ₁
      grind only [compTS, = ThinE.wk_id_toSubst, = VarE.subst_vz_lift, =_ compSTS_assoc, ThinE.comp,
        = ThinE.comp_toSubst, = TmE.ren_toSubst, TmE.subst, =_ compRen_wki, =_ ThinE.comp_wk_id,
        lift, =_ compST_toSubst, =_ ThinE.comp_wki_lift_eq_wk, = compSTT_assoc, =_ compTTS_assoc,
        =_ comp_toSubst_wk_id, = ThinE.wki_toSubst, = ThinE.id_comp,
        =_ ThinE.comp_wk_idi_lift_eq_wk, = ThinE.id_refold, = compSST_assoc, =_ ThinE.comp_assoc,
        = TmE.subst_ren_comp, =_ ThinE.comp_wki, toSubst, compST, = id_compST, =_ compSST_assoc,
        comp, = ThinE.comp_assoc, =_ TmE.subst_ren_comp, =_ comp_wki, VarE.subst,
        = ThinE.wk_toSubst, = compTS_wki_cons, TmE.ren_wki_step, wk, ThinE.wki]
      done

mutual
  /-- `A[δ][σ] = A[δ ∘ σ]` -/
  @[aesop norm] theorem TyE.subst_comp {γ θ δ : Nat} (A : TyE δ) (σ₂ : SubstE θ δ) (σ₁ : SubstE γ θ) : TyE.subst (TyE.subst A σ₂) σ₁ = TyE.subst A (SubstE.comp σ₂ σ₁) := by
    match A with
    | .U => rw [TyE.subst, TyE.subst, TyE.subst]
    | .El t => rw [TyE.subst, TyE.subst, TyE.subst, TmE.subst_comp]
    | .Pi A B =>
      rw [TyE.subst, TyE.subst, TyE.subst]
      /- ih_A : `A[δ][σ] = A[δ ∘ σ]` -/
      have ih_A : TyE.subst (TyE.subst A σ₂) σ₁ = TyE.subst A (SubstE.comp σ₂ σ₁) := TyE.subst_comp ..
      rw [ih_A]
      rw [TyE.subst_comp] -- ih_B : `B[lift δ][lift σ] = B[lift δ ∘ lift σ]`
      simp_all only [TyE.Pi.injEq, true_and]
      rw [SubstE.comp_lift]
    | .Sum A B => rw [TyE.subst, TyE.subst, TyE.subst, TyE.subst_comp, TyE.subst_comp]
    | .Unit => rfl
  -- termination_by sizeOf A + sizeOf σ₁ + sizeOf σ₂
  termination_by sizeOf A

  /-- `t[δ][σ] = t[δ ∘ σ]`. The full version of this is: `@substTm Γ Θ (substTy A σ) (@substTm Θ Δ A t σ) δ = substTy_comp ▸ @substTm Γ Δ A t (σ ∘ δ)` -/
  @[aesop norm] theorem TmE.subst_comp {γ θ δ} (t : TmE δ) (σ₂ : SubstE θ δ) (σ₁ : SubstE γ θ) : TmE.subst (TmE.subst t σ₂) σ₁ = TmE.subst t (SubstE.comp σ₂ σ₁) := by
    match t with
    | .var v =>
      rw [TmE.subst, TmE.subst]
      rw [VarE.subst_comp]
    | .app A B f a =>
      rw [TmE.subst]
      rw [TmE.subst]
      rw [TmE.subst]
      rw [TmE.subst_comp f]
      rw [TmE.subst_comp a]
      rw [TyE.subst_comp A]
      rw [TyE.subst_comp B] -- `B[lift δ][lift σ] = B[lift δ ∘ lift σ]`
      rw [SubstE.comp_lift]
    | .lam A B body =>
      rw [TmE.subst]
      rw [TmE.subst]
      rw [TmE.subst]
      rw [TmE.subst_comp body]
      rw [TyE.subst_comp A]
      rw [TyE.subst_comp B] -- `B[lift δ][lift σ] = B[lift δ ∘ lift σ]`
      rw [SubstE.comp_lift]
    | .pi A B =>
      rw [TmE.subst]
      rw [TmE.subst]
      rw [TmE.subst]
      rw [TmE.subst_comp A]
      rw [TmE.subst_comp B] -- `B[lift δ][lift σ] = B[lift δ ∘ lift σ]`
      rw [SubstE.comp_lift]
    | .left a => rw [TmE.subst, TmE.subst, TmE.subst, TmE.subst_comp]
    | .right b => rw [TmE.subst, TmE.subst, TmE.subst, TmE.subst_comp]
    | .elimSum A B Mot l r t =>
      rw [TmE.subst]
      rw [TmE.subst]
      rw [TmE.subst]
      rw [TyE.subst_comp]
      rw [TyE.subst_comp]
      rw [TyE.subst_comp]
      rw [TmE.subst_comp]
      rw [TmE.subst_comp]
      rw [TmE.subst_comp]
      rw [SubstE.comp_lift]
      done
    | .unit => rfl
  termination_by sizeOf t

  /-- `σ₁ ∘ (σ₂ ∘ σ₃) = (σ₁ ∘ σ₂) ∘ σ₃`, given `σ₁ : Subst Γ Θ₁`, `σ₂ : Subst Θ₁ Θ₂`, and `σ₃ : Subst Θ₂ Δ`.  -/
  @[aesop norm, grind =, grind =_] theorem SubstE.comp_assoc {γ θ₁ θ₂ δ : Nat}
    {σ₁ : SubstE γ θ₁}
    {σ₂ : SubstE θ₁ θ₂}
    {σ₃ : SubstE θ₂ δ}
    : σ₃ ∘ (σ₂ ∘ σ₁) = (σ₃ ∘ σ₂) ∘ σ₁ := by
      match σ₃ with
      | .nil => rfl
      | .cons σ₃ t =>
        --   `⟨σ, t⟩ ∘ (δ ∘ µ)`
        -- `= ⟨σ ∘ (δ ∘ µ), t[δ ∘ µ]⟩` by def ∘
        -- `= ⟨(σ ∘ δ) ∘ µ, t[δ ∘ μ]⟩` by induction hypothesis
        -- `= ⟨(σ ∘ δ) ∘ µ, t[δ][µ]⟩ ` by substTm_comp
        -- `= ⟨σ ∘ δ, t[δ]⟩ ∘ μ      ` by def ∘
        -- `= (σ ∘ δ) ∘ µ            ` by def ∘
        rw [SubstE.comp]
        rw [SubstE.comp]
        rw [SubstE.comp]
        rw [SubstE.comp_assoc]
        rw [TmE.subst_comp]
  termination_by sizeOf σ₃
end

#print axioms TmE.subst_comp

@[grind =, aesop norm] theorem TyE.ren_subst : TyE.ren (TyE.subst A σ₁) σ₂ = TyE.subst A (SubstE.comp σ₁ σ₂.toSubst) := by
  grind only [= subst_ren_comp, = SubstE.compST_toSubst, = ren_toSubst]
@[grind =, aesop norm] theorem TyE.subst_ren : TyE.subst (TyE.ren A σ₁) σ₂ = TyE.subst A (SubstE.comp σ₁.toSubst σ₂) := by
  grind only [= thin_subst_comp, = ren_toSubst, = SubstE.compTS_toSubst]
@[grind =, aesop norm] theorem TmE.ren_subst : TmE.ren (TmE.subst t σ₁) σ₂ = TmE.subst t (SubstE.comp σ₁ σ₂.toSubst) := by
  grind only [= ren_toSubst, = SubstE.compST_toSubst, = subst_ren_comp]
@[grind =, aesop norm] theorem TmE.subst_ren : TmE.subst (TmE.ren t σ₁) σ₂ = TmE.subst t (SubstE.comp σ₁.toSubst σ₂) := by
  grind only [= thin_subst_comp, = ren_toSubst, = SubstE.compTS_toSubst]


mutual
  @[simp, grind =] theorem VarE.subst_id (v : VarE γ) : v.subst .id = .var v := by
    match γ, v with
    | γ + 1, .vz => rfl
    | γ + 1, .vs v =>
      rw [SubstE.id, SubstE.lift]
      rw [VarE.subst]
      rw [SubstE.wk]
      grind only [= ThinE.wk_id_toSubst, = TmE.ren_toSubst, =_ ThinE.comp_wk_id,
        = SubstE.compRen_wki, =_ SubstE.compST_toSubst, =_ ThinE.comp_wki_lift_eq_wk,
        = VarE.vs_eq_ren_wki, → VarE.wk_step, = ThinE.wki_toSubst, = VarE.ren_wk_eq_ren_vs_lift,
        = VarE.ren_wk_σ_eq_var_ren_wki, =_ ThinE.comp_wk_idi_lift_eq_wk, = SubstE.compSST_assoc,
        =_ VarE.subst_ren_comp, =_ ThinE.comp_wki, toSubst, = SubstE.comp_assoc,
        → VarE.subst_wk_eq_subst_wk_toSubst, = SubstE.id_compST, = VarE.ren_wki_eq_vs,
        =_ VarE.subst_σ_ren_wki_compRen, = ThinE.wk_toSubst, TmE.ren_wki_step,
        =_ VarE.subst_wk_eq_subst_ren_wki, VarE.ren, = VarE.ren_toSubst, ThinE.wki]

  @[simp, grind =] theorem TmE.subst_id (t : TmE γ) : t.subst .id = t := by
    match t with
    | .var v => exact VarE.subst_id v
    | .app A B f a =>
      rw [TmE.subst]
      rw [<- SubstE.id]
      rw [TyE.subst_id]
      rw [TmE.subst_id]
      rw [TmE.subst_id]
      rw [TyE.subst_id]
    | .lam A B body =>
      rw [TmE.subst]
      rw [<- SubstE.id]
      rw [TyE.subst_id]
      rw [TmE.subst_id]
      rw [TyE.subst_id]
    | .pi A B =>
      rw [TmE.subst]
      rw [<- SubstE.id]
      rw [TmE.subst_id]
      rw [TmE.subst_id]
    | .left a =>
      rw [TmE.subst]
      rw [TmE.subst_id]
    | .right b =>
      rw [TmE.subst]
      rw [TmE.subst_id]
    | .elimSum A B Mot l r t =>
      rw [TmE.subst]
      rw [<- SubstE.id]
      rw [TmE.subst_id]
      rw [TmE.subst_id]
      rw [TmE.subst_id]
      rw [TyE.subst_id]
      rw [TyE.subst_id]
      rw [TyE.subst_id]
    | .unit => rfl

  @[simp, grind =] theorem TyE.subst_id (A : TyE γ) : A.subst .id = A := by
    match A with
    | .U => rfl
    | .Pi A B =>
      rw [TyE.subst]
      rw [<- SubstE.id]
      rw [TyE.subst_id]
      rw [TyE.subst_id]
    | .El t =>
      rw [TyE.subst]
      rw [TmE.subst_id]
    | .Sum A B =>
      rw [TyE.subst]
      rw [TyE.subst_id]
      rw [TyE.subst_id]
    | .Unit => rfl
end

@[simp, grind =] theorem SubstE.id_comp {σ : SubstE γ δ} : SubstE.comp .id σ = σ := by
  match δ with
  | 0 =>
    cases σ
    rfl
  | δ+1 =>
    let .cons σ t := σ
    rw [id, lift, comp]
    have ih := id_comp (σ := σ)
    grind only [=_ compSTS_assoc, TmE.subst, =_ compRen_wki, =_ ThinE.comp_wk_id, =_ compST_toSubst,
      =_ ThinE.comp_wki_lift_eq_wk, =_ ThinE.comp_wk_idi_lift_eq_wk, = compSST_assoc,
      =_ ThinE.comp_wki, = comp_assoc, = id_compST, =_ comp_wki, = comp_wki_cons, =_ comp_assoc,
      VarE.subst, wk, ThinE.wki]

@[simp, grind =] theorem SubstE.comp_id {σ : SubstE γ δ} : SubstE.comp σ .id = σ := by
  match σ with
  | .nil => rfl
  | .cons σ t =>
    have ih := comp_id (σ := σ)
    rw [comp]
    simp_all only [TmE.subst_id]

@[aesop 80%, grind =] theorem SubstE.comp_lift_cons : (.lift σ) ∘ (.id ;; t) = σ ;; t := by
  rw [SubstE.lift]
  rw [SubstE.comp]
  congr 1
  rw [<- SubstE.comp_wki]
  rw [<- SubstE.wki]
  rw [<- SubstE.comp_assoc]
  grind only [= comp_id, =_ compSTS_assoc, =_ compRen_wki, =_ ThinE.comp_wk_id, =_ compST_toSubst,
    =_ ThinE.comp_wki_lift_eq_wk, wki, =_ ThinE.comp_wk_idi_lift_eq_wk, = compSST_assoc,
    =_ ThinE.comp_wki, = comp_wki, = comp_assoc, = id_compST, =_ compSST_assoc, =_ comp_wki,
    = comp_wki_cons, =_ comp_assoc, = id_comp, wk, ThinE.wki]

@[simp, grind =] theorem SubstE.comp_wk_cons : SubstE.wk σ ∘ (.id ;; a) = σ := by
  grind only [compTS, = ThinE.wk_id_toSubst, =_ compST_wki_lift, = comp_id, = compTSS_assoc,
    = ThinE.comp_id, = compST_id, =_ compSTS_assoc, ThinE.comp, = ThinE.comp_toSubst,
    = compST_toSubst, =_ compRen_wki, = compTS_wk_id_cons, = compSTS_assoc, =_ ThinE.comp_wk_id,
    = compRen_wki, =_ compST_toSubst, = compTTS_assoc, =_ compSTT_assoc, = ThinE.id_toSubst,
    =_ ThinE.comp_wki_lift_eq_wk, = compSTT_assoc, =_ compTTS_assoc, wki, =_ comp_toSubst_wk_id,
    = ThinE.wki_toSubst, = ThinE.id_comp, =_ ThinE.comp_wk_idi_lift_eq_wk, ThinE.id,
    = ThinE.id_refold, = compSST_assoc, = comp_wki, =_ ThinE.comp_assoc, =_ ThinE.comp_wki, toSubst,
    = comp_assoc, =_ compSST_assoc, = id_compST, = ThinE.comp_assoc, = comp_wki_cons, =_ comp_wki,
    =_ comp_assoc, = ThinE.lift_toSubst, = ThinE.wk_toSubst, = compTS_wki_cons, = id_comp, wk,
    =_ compST_wk_id_lift, =_ compTSS_assoc, = compTS_toSubst, ThinE.wki]

def VarE.thin : {γ δ : Nat} -> VarE δ -> ThinE γ δ -> VarE γ := VarE.ren
def TmE.thin : {γ δ : Nat} -> TmE δ -> ThinE γ δ -> TmE γ := TmE.ren
def TyE.thin : {γ δ : Nat} -> TyE δ -> ThinE γ δ -> TyE γ := TyE.ren
