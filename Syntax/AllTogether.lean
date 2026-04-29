import Aesop
import Qq
import Lean
import Syntax.Erased
import Syntax.Wellformed

set_option linter.unusedVariables false
set_option pp.fieldNotation.generalized false

/-
  # All Together
-/

def Con                      := (γ : Nat) × {Γ : ConE γ // ConW Γ}
def Ty (Γ : Con)             := { A : TyE Γ.1           // TyW Γ.2.1 A }
def Var (Γ : Con) (A : Ty Γ) := { v : VarE Γ.1          // VarW Γ.2.1 A.1 v }
def Tm (Γ : Con) (A : Ty Γ)  := { t : TmE Γ.1           // TmW Γ.2.1 A.1 t }
def Thin (Γ Δ : Con)         := { σ : ThinE Γ.1 Δ.1     // ThinW Γ.2.1 Δ.2.1 σ }
def Subst (Γ Δ : Con)        := { σ : SubstE Γ.1 Δ.1    // SubstW Γ.2.1 Δ.2.1 σ }
def ConConv (Γ Δ : Con) : Prop   := ConWConv Γ.2.1 Δ.2.1
def TyConv (A B : Ty Γ) : Prop   := TyWConv Γ.2.1 A.1 B.1
def TmConv (t u : Tm Γ A) : Prop := TmWConv Γ.2.1 A.1 t.1 u.1


def Con.len (Γ : Con) : Nat := Γ.1
def Con.e (Γ : Con) : ConE Γ.len := Γ.2.1
def Con.w (Γ : Con) : ConW Γ.e := Γ.2.2

instance : Coe Con Nat := ⟨(·.1)⟩
instance : CoeDep Con Γ (ConE Γ.1) := ⟨Γ.2.1⟩
instance : CoeDep Con Γ (ConW Γ.2.1) := ⟨Γ.2.2⟩

def Con.nil : Con                                                                            := ⟨0    , .nil      , .nil⟩
def Con.ext (Γ : Con) (A : Ty Γ) : Con                                                       := ⟨Γ + 1, .ext Γ A.1, .ext Γ.2.2 A.2⟩

def Ty.U : Ty Γ                                                                              := ⟨.U, .U Γ.2.2⟩
def Ty.El (t : Tm Γ .U) : Ty Γ                                                               := ⟨.El t.1, .El Γ t.2⟩
def Ty.Pi (A : Ty Γ) (B : Ty (.ext Γ A)) : Ty Γ                                              := ⟨.Pi A.1 B.1, .Pi Γ A.2 B.2⟩
def Ty.Sum (A B : Ty Γ) : Ty Γ                                                               := ⟨.Sum A.1 B.1, .Sum Γ A.2 B.2⟩
def Ty.Unit : Ty Γ                                                                           := ⟨.Unit, .Unit Γ⟩

def Ty.subst {Γ Δ : Con} (A : Ty Δ) (σ : Subst Γ Δ) : Ty Γ                                    := ⟨.subst      A.1 σ.1, TyW.subst Γ Δ A.2 σ.2⟩
def Tm.subst {Γ Δ : Con} {A : Ty Δ} (t : Tm Δ A) (σ : Subst Γ Δ) : Tm Γ (Ty.subst A σ)         := ⟨.subst      t.1 σ.1, TmW.subst Γ Δ A.2 t.2 σ.2⟩

def Subst.nil : Subst Γ Con.nil                                                              := ⟨.nil, .nil Γ⟩
def Subst.cons (δ : Subst Γ Δ) (t : Tm Γ (Ty.subst A δ)) : Subst Γ (Δ.ext A)                  := ⟨.cons .., .cons Γ Δ A.2 δ.2 t.2⟩
def Subst.comp {Γ Θ Δ : Con} (δ : Subst Θ Δ) (σ : Subst Γ Θ) : Subst Γ Δ                           := ⟨.comp δ.1 σ.1, .comp Γ.w Θ.w Δ.w δ.2 σ.2⟩
def Subst.wk (σ : Subst Γ Δ) : Subst (.ext Γ W) Δ                                            := ⟨.wk σ.1, .wk W.2 σ.2⟩
/-- `lift σ := ⟨wk σ, #0⟩` -/
def Subst.lift (σ : Subst Γ Δ) : Subst (.ext Γ (W.subst σ)) (.ext Δ W)                     := ⟨.lift σ.1, .lift W.2 σ.2⟩
def Subst.id : Subst Γ Γ                                                                     := ⟨.id, .id Γ.w⟩
def Subst.wki : Subst (.ext Γ W) Γ                                                             := ⟨.wki, .wki W.2⟩



@[aesop safe] theorem ConConv.same_len {Γ Δ : Con} (c : ConConv Γ Δ) : Γ.1 = Δ.1 := ConWConv.same_len c

def Tm.conv {A B : Ty Γ} (c : TyConv A B) (t : Tm Γ A) : Tm Γ B                                     := ⟨t.1, TmW.conv Γ.2.2 Γ.2.2 A.2 B.2 (.refl Γ.2.2) c t.2⟩

/-- This is ugly due to having to use `ConConv.same_len` and thus a cast on preterms.
  Only use this in proofs, and not in computationally relevant places. -/
def Ty.conv {Γ₁ Γ₂ : Con} (Γc : ConConv Γ₁ Γ₂) (A : Ty Γ₁) : Ty Γ₂ :=
  have same_len := Γc.same_len
  let ⟨γ1, Γ1e, Γ1w⟩ := Γ₁
  let ⟨γ2, Γ2e, Γ2w⟩ := Γ₂
  let ⟨Ae, Aw⟩ := A
  ⟨
    same_len ▸ Ae,
    by
      cases same_len
      have h := Aw.conv Γc
      exact h
  ⟩

@[aesop 10%] theorem TyConv.ofEq {A B : Ty Γ} (h : A = B) : TyConv A B := h ▸ TyWConv.refl Γ.2.2 A.2
@[aesop 10%] theorem TmConv.ofEq {x y : Tm Γ A} (h : x = y) : TmConv x y := h ▸ TmWConv.refl Γ.2.2 A.2 x.2
instance {Γ} {A B : Ty Γ} : Coe (Eq A B) (TyConv A B) := ⟨.ofEq⟩

@[aesop forward 1%] theorem Ty.cast {Γ Δ : Con} (h : ConConv Γ Δ) : Ty Γ = Ty Δ := by
  dsimp [Ty]
  have ⟨γ, Γ, Γw⟩ := Γ
  have ⟨δ, Δ, Δw⟩ := Δ
  cases ConWConv.same_len h
  dsimp at *
  congr 1
  ext A
  rw [TyW.cast Γw Δw h]

@[aesop forward 1%] theorem Tm.cast {A B : Ty Γ} (h : TyConv A B) : Tm Γ A = Tm Γ B := by
  dsimp [Tm]
  congr 1
  ext t
  rw [TmW.cast Γ.2.2 A.2 B.2]
  exact h

-- We have `Tm Γ "id A" = Tm Γ "A"`, but inhabitants are distinct, so `"id x" : Tm Γ "A"` is different from `"x"`.

#print axioms Tm.cast -- propext, Quot.sound

namespace Notation
  scoped notation (name := empStx) "[]" => Con.nil
  scoped infixl:66 (name := extStx) "; " => Con.ext
  scoped infixl:69 (name := consStx) " ;; " => Subst.cons
  scoped notation (name := nilStx) "⟨;;⟩" => Subst.nil
  scoped infixl:67 (name := SumStx) " + " => Ty.Sum

  scoped notation:max (name := substTyStx) (priority := high) A:max "[" σ "]" => Ty.subst A σ
  scoped notation:max (name := substTmStx) (priority := high) t:max "[" σ "]" => Tm.subst t σ
  scoped infixl:70 (name := compStx) (priority := high) " ∘ " => Subst.comp

  scoped notation:50 (name := convTyStx') Γ " ⊢ " A " ≅ " B => @TyConv Γ A B
  scoped notation:50 (name := convTmStx') Γ " ⊢ " x " ≅ " y " : " A => @TmConv Γ A x y
end Notation
open Notation
open Subst (wki id wk lift cons)

@[simp, grind =] theorem Ty.subst_id {A : Ty Γ} : A[.id] = A := by
  let ⟨Ae, Aw⟩ := A
  rw [Ty.subst, Subst.id]; dsimp
  congr 1
  exact TyE.subst_id Ae

def Subst.apply (a : Tm Γ A) : Subst Γ (Γ.ext A) := .id ;; (a.conv (.ofEq Ty.subst_id.symm))

/-- This version was shown in the thesis: -/
def Subst.apply.as_per_thesis {a : Tm Γ A} : Subst Γ (Γ; A) := .id ;; ⟨a.1, he ▸ a.2⟩
where
  he : TmW Γ A.1 a.1 = TmW Γ (.subst A.1 .id) a.1 := by
    congr
    exact TyE.subst_id A.1 |>.symm

/-- `vz {Γ} {A : Ty Γ} : Var (Γ, A) A[wki]`. -/
def Var.vz : Var (.ext Γ A) (A.subst .wki)  :=
  ⟨.vz, by
          have h := VarW.vz Γ.w A.2
          simp_all only [ThinE.wki, TyE.ren_toSubst, ThinE.wk_toSubst, ThinE.id_toSubst]
          exact h
  ⟩

/-- `vs {Γ} {A : Ty Γ} {B : Ty Γ} : Var Γ A -> Var (Γ, B) A[wki]`. -/
def Var.vs (v : Var Γ A) : Var (.ext Γ B) (A.subst .wki) :=
  ⟨.vs v.1, by
    have h := VarW.vs Γ.w A.2 B.2 v.2
    simp_all only [ThinE.wki, TyE.ren_toSubst, ThinE.wk_toSubst, ThinE.id_toSubst]
    exact h
  ⟩

def Tm.var {Γ} {A : Ty Γ} (v : Var Γ A) : Tm Γ A := ⟨.var v.1, .var Γ.2.2 A.2 v.2⟩

set_option pp.proofs true in
/-- `Tm.app {A : Ty Γ} {B : Ty (Γ; A)} (f : Tm Γ (.Pi A B)) (a : Tm Γ A) : Tm Γ B[⟨id, a⟩]` -/
def Tm.app {A : Ty Γ} {B : Ty (Γ.ext A)} (f : Tm Γ (.Pi A B)) (a : Tm Γ A) : Tm Γ (B.subst (.apply a)) :=
  ⟨.app A.1 B.1 f.1 a.1, .app Γ A.2 B.2 f.2 a.2⟩

set_option pp.proofs true in
/-- `Tm.app {A : Ty Γ} {B : Ty (Γ; A)} (f : Tm Γ (.Pi A B)) (a : Tm Γ A) : Tm Γ B[⟨id, a⟩]` -/
def Tm.app.as_per_thesis {A : Ty Γ} {B : Ty (Γ.ext A)} (f : Tm Γ (.Pi A B)) (a : Tm Γ A) : Tm Γ (B.subst (Subst.apply.as_per_thesis (a := a))) :=
  ⟨.app A.1 B.1 f.1 a.1, .app Γ A.2 B.2 f.2 a.2⟩

def Tm.lam {Γ} {A : Ty Γ} {B : Ty (.ext Γ A)} (body : Tm (.ext Γ A) B) : Tm Γ (.Pi A B)             := ⟨.lam .., .lam Γ A.2 B.2 body.2⟩

/-- `Γ ⊢ A : U` and `Γ;A ⊢ B : U` thus `Γ ⊢ A -> B : U`. -/
def Tm.pi (A : Tm Γ .U) (B : Tm (.ext Γ (.El A)) .U) : Tm Γ .U := ⟨.pi A.1 B.1, .pi Γ A.2 B.2⟩

def Tm.left (a : Tm Γ A) : Tm Γ (.Sum A B) := ⟨.left a.1, .left Γ A.2 B.2 a.2⟩
def Tm.right {Γ A B} (b : Tm Γ B) : Tm Γ (.Sum A B) := ⟨.right b.1, .right Γ A.2 B.2 b.2⟩

/-- Eliminator for sum types. Ignoring substitution shuffling, from\
  `Γ; A+B ⊢ Mot`\
  `Γ; A   ⊢ leftM  : Mot[wki ;; .left #0]`\
  `Γ; B   ⊢ rightM : Mot[wki ;; .right #0]`\
  `Γ      ⊢ t : A + B`\
  follows\
  `Γ ⊢ elimSum Mot leftM rightM t : Mot[t]` -/
def Tm.elimSum (Mot : Ty (Γ; A+B))
  (leftM  : Tm (Γ; A) Mot[wki ;; (.left  (.var .vz) : Tm (Γ; A) (A[wki] + B[wki]))])  -- apparently we really need this type annotation
  (rightM : Tm (Γ; B) Mot[wki ;; (.right (.var .vz) : Tm (Γ; B) (A[wki] + B[wki]))])
  (t : Tm Γ (A + B))
  : Tm Γ Mot[.apply t]
  := ⟨.elimSum A.1 B.1 Mot.1 leftM.1 rightM.1 t.1, .elimSum Γ A.2 B.2 Mot.2 leftM.2 rightM.2 t.2⟩

def Tm.unit : Tm Γ .Unit := ⟨.unit, .unit Γ⟩

def Ty.Bool : Ty Γ        := .Sum .Unit .Unit
def Tm.false : Tm Γ .Bool := .left .unit
def Tm.true : Tm Γ .Bool  := .right .unit


section Helpers
  /-- Just a convenience definition `⟨wki ;; .left #0⟩` -/
  def Subst.left  : Subst (Γ; A) (Γ; A+B) := (wki ;; (.left  (.var .vz) : Tm (Γ; A) (A[wki] + B[wki])))
  def Subst.right : Subst (Γ; B) (Γ; A+B) := (wki ;; (.right (.var .vz) : Tm (Γ; B) (A[wki] + B[wki])))

  def Subst.wk2 {Γ A B}   : Subst (Γ; A; B   ) Γ := wk wki
  def Subst.wk3 {Γ A B C} : Subst (Γ; A; B; C) Γ := wk wk2

  def Tm.app2 (f : Tm Γ (.Pi A (.Pi B C))) (a : Tm Γ A) (b : Tm Γ B[.apply a])
    : Tm Γ C[Subst.lift (Subst.apply a)][Subst.apply b]
    :=
      -- We don't need these `let`s, but they are illustrative:
      -- let fa : Tm Γ (.Pi B           C                   )[.apply a] := Tm.app f a
      -- let fa : Tm Γ (.Pi B[.apply a] C[.lift <| .apply a])           := Tm.app f a
      Tm.app (.app f a) b

  def Tm.app3
    (f : Tm Γ (.Pi A (.Pi B (.Pi C D))))
    (a : Tm Γ A)
    (b : Tm Γ B[.apply a])
    (c : Tm Γ C[.lift (.apply a)][.apply b])
    : Tm Γ D[.lift (.lift (.apply a))][.lift (.apply b)][.apply c]
    :=
      -- app (app (app f a) b) c -- doesn't work directly, need to help with `let`
      let fa   : Tm Γ (.Pi B           (.Pi C D)                   )[.apply a] := Tm.app f a
      let fa   : Tm Γ (.Pi B[.apply a] (.Pi C D)[.lift <| .apply a])           := Tm.app f a
      let fab  : Tm Γ (.Pi C                             D                                              )[.lift (.apply a)][.apply b] := Tm.app (.app f a) b
      let fab  : Tm Γ (.Pi C[.lift (.apply a)]           D[.lift <| .lift (.apply a)]                   )[.apply b]                   := Tm.app (.app f a) b
      let fab  : Tm Γ (.Pi C[.lift (.apply a)][.apply b] D[.lift <| .lift (.apply a)][.lift <| .apply b])                             := fab
      let fabc := Tm.app fab c
      fabc
end Helpers

@[aesop norm] def Ty.Sum.subst_into {A B : Ty Γ} : (A + B)[σ] = A[σ] + B[σ] := rfl

section SubstTheorems

variable {Γ Θ Δ : Con}
variable {σ : Subst Γ Δ}
variable {A : Ty Δ}
variable {σ₁ : Subst Θ Δ} {σ₂ : Subst Γ Θ}

@[aesop 90%, grind =, grind =_] theorem Ty.subst_comp : A[σ₁][σ₂] = A[σ₁ ∘ σ₂] := by
  dsimp [subst, Subst.comp]
  congr 1
  exact TyE.subst_comp ..

@[aesop 90%, grind =] theorem Tm.subst_comp {t : Tm Δ A} : t[σ₁][σ₂] = t[σ₁ ∘ σ₂].conv (.ofEq Ty.subst_comp.symm) := by
  dsimp [subst, Subst.comp]
  dsimp [conv] -- * The "cast" via conv is not an issue here :)
               -- ^ If we had used `Eq.rec`, this cast wouldn't just compute away into the wellformedness half.
  congr 1
  exact TmE.subst_comp .. -- * We just delegate to the E proofs

@[aesop 90%, grind =] theorem Subst.lift_comp {σ₁ : Subst Θ Δ} {σ₂ : Subst Γ Θ} : (lift (W := W) σ₁ ∘ lift σ₂) = Ty.subst_comp ▸ lift (σ₁ ∘ σ₂) := by
  -- By delegating to corresponding E proof.
  -- In the future we will hide the cast in the W half as well.
  sorry

@[aesop 70%, grind =] theorem Subst.comp_cons {t : Tm Θ A[σ₁]} : (σ₁ ;; t) ∘ σ₂ = (σ₁ ∘ σ₂ ;; (t[σ₂]).conv (.ofEq Ty.subst_comp)) := rfl
@[simp, grind =] theorem Subst.comp_nil : .nil ∘ σ₂ = .nil := rfl

@[grind =, grind =_, aesop 20%] theorem Subst.comp_wk : σ ∘ (.wk (W := W) .id) = .wk σ := by
  dsimp [comp, wk, wk, id]
  congr 1
  exact SubstE.comp_wki σ.val

set_option backward.isDefEq.respectTransparency false in
@[aesop 50%, grind =, grind =_] theorem Ty.subst_wk : A[σ][wki (W := W)] = A[wk σ] := by
  dsimp [Ty.subst, Subst.wki, Subst.wk]
  congr 1
  simp_all only [SubstE.wki, TyE.subst_comp, SubstE.comp_wki σ.val]

@[aesop 5%, grind =] theorem Subst.lift_eq {W : Ty Δ} : Subst.lift σ = Subst.cons (Subst.wk (W := W[σ]) σ) ((.var .vz : Tm _ _).conv (.ofEq Ty.subst_wk)) := by rfl

theorem Subst.left_apply {Γ : Con} {A B : Ty Γ} {a : Tm Γ A} : (@Subst.left Γ A B) ∘ (.apply a) = .apply (.left a) := by
  rw [Subst.left]
  rw [Subst.comp_cons]
  rw [apply, apply]
  sorry

theorem Subst.left_apply' {Γ : Con} {A B : Ty Γ} {a : Tm Γ A} {Mot : Ty _} : Mot[@Subst.left Γ A B][.apply a] = Mot[.apply (.left a)] := by sorry

set_option backward.isDefEq.respectTransparency false in
/-- `wki ∘ ⟨σ, a⟩ = σ` -/
@[simp, grind =, aesop safe] theorem Subst.comp_wki_cons : Subst.wki ∘ (σ ;; t) = σ := by
  let ⟨σ, σw⟩ := σ
  dsimp [wki, wk, id, cons, comp]
  congr 1
  rw [SubstE.wki]
  simp_all only [SubstE.comp_wki_cons]

/-- `wki ∘ ⟨id, a⟩ = .id` -/
@[simp, grind =, aesop safe] theorem Subst.comp_wki_apply : Subst.wki ∘ (.apply val) = .id := by rw [apply]; simp_all only [comp_wki_cons]

/-- `B[wk id][⟨id, a⟩] = B` -/
@[simp] theorem Ty.subst_wki_apply {B : Ty Γ} : (B.subst .wki).subst (.apply val) = B := by
  rw [Ty.subst_comp]
  rw [Subst.comp_wki_apply]
  rw [Ty.subst_id]

/-- Let binders. This is a conservative extension. -/
-- @[irreducible]
def Tm.letE {Γ : Con} {A B : Ty Γ} (val : Tm Γ A) (body : Tm (Γ.ext A) (B.subst .wki)) : Tm Γ B     := body.subst (.apply val) |>.conv (.ofEq Ty.subst_wki_apply)

set_option backward.isDefEq.respectTransparency false in
@[grind =, aesop 20%] theorem Subst.comp_lift_apply {σ : Subst Γ Δ} : lift σ ∘ apply a[σ] = apply a ∘ σ := by
  rw [apply]
  rw [apply]
  -- Instead of unfolding by `comp`, which would get into into erased term territory, we can use `comp_cons` to get a nicer goal:
  rw [comp_cons]
  dsimp [lift, comp, cons, id, Tm.conv, Tm.subst, Ty.subst]
  congr 1
  rw [SubstE.id_comp]
  rw [SubstE.lift]
  rw [SubstE.comp]
  simp_all only [SubstE.comp_wk_cons, TmE.subst, VarE.subst.eq_1]

@[grind =, grind =_, aesop 50%] theorem Ty.subst_lift_apply {B : Ty (Δ; A)} : B[lift σ][.apply a[σ]] = B[.apply a][σ] := by
  grind only [= Subst.comp_cons, = subst_comp, = Subst.lift_eq, =_ subst_wk, =_ Subst.comp_wk,
    = Subst.comp_lift_apply]

theorem TyConv.subst_lift_apply {σ : Subst Γ Δ} {A} {B : Ty (Δ; A)} {a} : TyConv B[lift σ][.apply a[σ]] B[.apply a][σ] := .ofEq Ty.subst_lift_apply

@[simp, grind =, aesop norm] theorem Ty.U_subst : (Ty.U)[σ] = .U := rfl
@[grind =, aesop 90%] theorem Ty.El_subst : (Ty.El t)[σ] = Ty.El t[σ] := rfl
@[grind =, aesop 90%] theorem Ty.Pi_subst : (Ty.Pi A B)[σ] = Ty.Pi A[σ] B[.lift σ] := rfl

@[aesop 90%, grind =] theorem Tm.lam_subst {Γ Δ A B b} {σ : Subst Γ Δ} : (@Tm.lam Δ A B b)[σ] = @Tm.lam Γ A[σ] B[.lift σ] b[.lift σ] := rfl
@[aesop 90%, grind =] theorem Tm.app_subst {Γ Δ A B f a} {σ : Subst Γ Δ}
  : (@Tm.app Δ A B f a)[σ] = (@Tm.app Γ A[σ] B[.lift σ] f[σ] a[σ]).conv (.ofEq Ty.subst_lift_apply)
  := rfl

-- This theorem looks scary, but it is not:
-- The lengthy proofs get lifted into their own definitions by lean anyway,
-- and due to proof irrelevance we can ignore the long proofs.
@[aesop 90%, grind =]
theorem Tm.elimSum_subst {Γ Δ A B M l r t} {σ : Subst Γ Δ}
  : (@Tm.elimSum Δ A B M l r t)[σ]
  = (
      @Tm.elimSum Γ A[σ] B[σ] M[.lift σ]
        (conv  (.ofEq (by
            rw [Ty.subst_comp, Ty.subst_comp]
            dsimp only [wki, left, cons, Subst.comp, Tm.var, Var.vz, lift, Ty.subst, Con.ext]
            congr 1
            grind only [= SubstE.compTS.eq_2, = ThinE.wk_id_toSubst, = VarE.subst_vz_lift, = SubstE.comp_id, =_ SubstE.compSTS_assoc, = ThinE.comp.eq_1, = ThinE.comp_toSubst, = TmE.subst.eq_1, =_ SubstE.compRen_wki, = SubstE.compTS_wk_id_cons, =_ ThinE.comp_wk_id, = SubstE.lift.eq_1, = SubstE.compRen_wki, =_ SubstE.compST_toSubst, =_ ThinE.comp_wki_lift_eq_wk, = SubstE.compSTT_assoc, =_ SubstE.compTTS_assoc, = SubstE.comp_wki_lift, =_ SubstE.comp_toSubst_wk_id, = ThinE.wki_toSubst, = SubstE.wki.eq_1, = ThinE.id_comp, =_ ThinE.comp_wk_idi_lift_eq_wk, = ThinE.id_refold, = SubstE.compSST_assoc, =_ ThinE.comp_assoc, = SubstE.comp_wki, =_ ThinE.comp_wki, = ThinE.toSubst.eq_2, = SubstE.comp_assoc, = SubstE.id_compST, = SubstE.comp.eq_2, = ThinE.comp_assoc, = SubstE.comp_wki_cons, =_ SubstE.comp_wki, = ThinE.comp.eq_4, =_ SubstE.comp_assoc, = VarE.subst.eq_1, = ThinE.wk_toSubst, = SubstE.compTS_wki_cons, = SubstE.id_comp, = SubstE.wk.eq_1, = TmE.subst.eq_5, = SubstE.compTS_toSubst, ThinE.wki]
          )) l[.lift σ])
        (conv  (.ofEq (by
            rw [Ty.subst_comp, Ty.subst_comp]
            dsimp only [wki, right, cons, Subst.comp, Tm.var, Var.vz, lift, Ty.subst, Con.ext]
            congr 1
            grind only [= SubstE.compTS.eq_2, = ThinE.wk_id_toSubst, = VarE.subst_vz_lift, = SubstE.comp_id, =_ SubstE.compSTS_assoc, = ThinE.comp.eq_1, = ThinE.comp_toSubst, = TmE.subst.eq_1, =_ SubstE.compRen_wki, = SubstE.compTS_wk_id_cons, =_ ThinE.comp_wk_id, = SubstE.lift.eq_1, = SubstE.compRen_wki, =_ SubstE.compST_toSubst, =_ ThinE.comp_wki_lift_eq_wk, = SubstE.compSTT_assoc, =_ SubstE.compTTS_assoc, = SubstE.comp_wki_lift, =_ SubstE.comp_toSubst_wk_id, = ThinE.wki_toSubst, = SubstE.wki.eq_1, = ThinE.id_comp, =_ ThinE.comp_wk_idi_lift_eq_wk, = ThinE.id_refold, = SubstE.compSST_assoc, =_ ThinE.comp_assoc, = SubstE.comp_wki, =_ ThinE.comp_wki, = ThinE.toSubst.eq_2, = SubstE.comp_assoc, = TmE.subst.eq_6, = SubstE.id_compST, = SubstE.comp.eq_2, = ThinE.comp_assoc, = SubstE.comp_wki_cons, =_ SubstE.comp_wki, = ThinE.comp.eq_4, =_ SubstE.comp_assoc, = VarE.subst.eq_1, = ThinE.wk_toSubst, = SubstE.compTS_wki_cons, = SubstE.id_comp, = SubstE.wk.eq_1, = SubstE.compTS_toSubst, ThinE.wki]
          )) r[.lift σ])
        t[σ]
    ).conv (.ofEq Ty.subst_lift_apply)
  := by rfl

end SubstTheorems


/-
  ## Computation Rules
-/

def ConConv.refl : ConConv Γ Γ := ConWConv.refl Γ.2.2
def ConConv.ext' {A A' : Ty Γ} (Ac : TyConv A A') : ConConv (.ext Γ A) (.ext Γ A') := ConWConv.ext (.refl Γ.2.2) Ac

@[aesop 10%] def TyConv.symm : TyConv x y -> TyConv y x := TyWConv.symm
@[aesop safe] def TyConv.refl {X : Ty Γ} : TyConv X X := TyWConv.refl Γ X.2
@[aesop safe forward, aesop 50%] def TyConv.trans {X Y Z : Ty Γ} : TyConv X Y -> TyConv Y Z -> TyConv X Z := TyWConv.trans Γ X.2 Y.2 Z.2
@[aesop 50%] def TyConv.subst {X Y : Ty Δ} (c : @TyConv Δ X Y) (σ) : @TyConv Γ X[σ] Y[σ] := TyWConv.subst Γ σ.2 c

@[aesop 10%] def TyConv.Pi {A A' : Ty Γ} {B : Ty (Γ; A)} {B' : Ty (Γ; A')}
  : (Ac : TyConv A A') -> @TyConv (Γ.ext A) B (B'.conv (.ext' Ac.symm)) -> TyConv (.Pi A B) (.Pi A' B')
  := TyWConv.Pi Γ.w A.2 A'.2 B.2 B'.2

@[aesop 10%] def TmConv.symm : TmConv x y -> TmConv y x := TmWConv.symm
@[aesop safe] def TmConv.refl {x : Tm Γ A} : TmConv x x := TmWConv.refl Γ A.2 x.2
@[aesop safe forward, aesop 50%] def TmConv.trans : TmConv x y -> TmConv y z -> TmConv x z := TmWConv.trans

@[simp] theorem Tm.conv_collapse {A B C : Ty Γ} {t} {c1 : Γ ⊢ A ≅ B} {c2 : Γ ⊢ B ≅ C} : Tm.conv c2 (Tm.conv c1 t) = Tm.conv (.trans c1 c2) t := rfl
@[simp] theorem Tm.conv_subst : (Tm.conv c t)[σ] = Tm.conv (c.subst σ) t[σ] := rfl

/-- `Γ ⊢ (λx. b) a : B[a]` converts to `Γ ⊢ b[a] : B[a]`. -/
@[aesop 33%] def TmConv.beta (b : Tm (.ext Γ A) B) (a : Tm Γ A)
  : @TmConv Γ (B.subst _) (.app (.lam b) a) (b.subst (.apply a))
  := TmWConv.beta Γ.2.2 A.2 B.2 a.2 b.2

/-- A small helper to guide aesop. `b[a] ≅ RHS -> .app (.lam b) a ≅ RHS` -/
@[aesop safe] def TmConv.beta_redLeft {b : Tm (.ext Γ A) B} {a : Tm Γ A} {RHS} :
  @TmConv Γ (B.subst _) (b.subst (.apply a)) RHS ->
  @TmConv Γ (B.subst _) (.app (.lam b) a) RHS
  := by
    have bt : _ ⊢ Tm.app (Tm.lam b) a ≅ b[Subst.apply a] : _ := beta _ _
    intro a_1
    have fwd : _ ⊢ Tm.app (Tm.lam b) a ≅ RHS : _ := trans (y := b[Subst.apply a]) bt a_1
    simp_all only

@[aesop 1%] theorem TmConv.rhs : TmConv R R' -> TmConv L R' -> TmConv L R := by
  intro r h
  exact h.trans r.symm

/-- A small helper to guide aesop. `LHS ≅ b[a] -> LHS ≅ .app (.lam b) a` -/
@[aesop safe] def TmConv.beta_redRight {b : Tm (.ext Γ A) B} {a : Tm Γ A} {LHS} :
  @TmConv Γ (B.subst (.apply a)) LHS (b.subst (.apply a)) ->
  @TmConv Γ (B.subst (.apply a)) LHS (.app (.lam b) a)
  := by
    have bt : _ ⊢ Tm.app (Tm.lam b) a ≅ b[Subst.apply a] : _ := beta _ _
    intro a_1
    apply TmConv.symm
    apply TmConv.beta_redLeft
    apply TmConv.symm
    simp_all only

/-- A small helper to guide aesop. `LHS ≅ b[a] -> LHS ≅ .app (.lam b) a` -/
@[aesop safe] def TmConv.beta_redRight' {b : Tm (.ext Γ A) B} {a : Tm Γ A} {LHS} :
  (c : _ ⊢ B[.apply a] ≅ C) ->
  @TmConv Γ C LHS ((b.subst (.apply a)).conv c) ->
  @TmConv Γ C LHS ((Tm.app (.lam b) a).conv c)
  := by
    intro c h
    have bt : Γ ⊢ Tm.app (Tm.lam b) a ≅ b[Subst.apply a] : _ := beta _ _
    apply TmConv.symm
    sorry


@[aesop safe] def TyConv.El {t t' : Tm Γ .U} : TmConv t t' -> TyConv (.El t) (.El t') := TyWConv.El Γ t.2 t'.2

/-- Reduction rule for sum types.

  We have `Γ; A   ⊢ leftM  : Mot[⟨id, left #0⟩]`
  Then `Γ ⊢ leftM[⟨id, a⟩] : Mot[⟨id, left #0⟩][⟨id, a⟩]`
  Where the type should compute as follows...
    `Mot[⟨id, left #0⟩][⟨id, a⟩]`
  = `Mot[⟨id, left #0⟩ ∘ ⟨id, a⟩]`
  = `Mot[⟨id, left a⟩]`.
  Therefore we should have
    `Γ ⊢ leftM[⟨id, a⟩] : Mot[⟨id, left a⟩]`
-/
theorem TmConv.sum_left {Γ} {A B : Ty Γ} {Mot : Ty (Γ; (A + B))}
  {leftM : Tm (Γ; A) Mot[.left]}
  {rightM : Tm (Γ; B) Mot[.right]}
  {a : Tm Γ A}
  : @TmConv Γ Mot[.apply (.left a)]
      (.elimSum Mot leftM rightM (.left a))
      (.conv (.ofEq Subst.left_apply') leftM[.apply a])
  := TmWConv.sum_left Γ.2.2 A.2 B.2 Mot.2 leftM.2 rightM.2 a.2

theorem TmConv.left_congr {Γ A B} {x y : Tm Γ A} (c : TmConv x y) : @TmConv Γ (A + B) (.left x) (.left y) := by
  sorry

section ConvImplicit
-- Idea: What if we put Tm.conv *everywhere*, and hide it by making it implicit?
-- We always know how to construct conversion proofs on the rhs, given conversion proofs on the lhs.

def Tm.substC {Γ Δ : Con} {A : Ty Δ} (t : Tm Δ A) (σ : Subst Γ Δ) {C} {c : TyConv A[σ] C} : Tm Γ C := t[σ] |>.conv c

def Tm.appC (f : Tm Γ (.Pi A B)) (a : Tm Γ A) {C} {c : TyConv B[.apply a] C} : Tm Γ C := Tm.app f a |>.conv c
def Tm.lamC (b : Tm (Γ; A) B) {C} {c : TyConv (.Pi A B) C} : Tm Γ C := Tm.lam b |>.conv c
def Tm.elimSumC (Mot : Ty (Γ; A+B))
  (leftM  : Tm (Γ; A) Mot[wki ;; (.left  (.var .vz) : Tm (Γ; A) (A[wki] + B[wki]))])
  (rightM : Tm (Γ; B) Mot[wki ;; (.right (.var .vz) : Tm (Γ; B) (A[wki] + B[wki]))])
  (t : Tm Γ (A + B))
  {C} {c : TyConv Mot[.apply t] C}
  : Tm Γ C
  := Tm.elimSum Mot leftM rightM t |>.conv c


theorem Tm.appC_subst' {Γ Δ A B f a} {σ : Subst Γ Δ} {C c}
  : (@Tm.appC Δ A B f a C c)[σ]
  = @Tm.appC Γ A[σ] B[.lift σ] f[σ] a[σ] C[σ] ((TyConv.ofEq Ty.subst_lift_apply).trans (TyConv.subst c σ))
  := rfl

theorem Tm.appC_subst {Γ Δ A B f a} {σ : Subst Γ Δ} {C1 c1} {C2} {c2 : TyConv C1[σ] C2}
  : Tm.substC (@Tm.appC Δ A B f a C1 c1) σ (c := c2)
  = @Tm.appC Γ A[σ] B[.lift σ] f[σ] a[σ] C2 (TyConv.ofEq Ty.subst_lift_apply |>.trans (TyConv.subst c1 σ) |>.trans c2)
  := rfl

theorem Tm.elimSumC_subst {Γ Δ A B M l r t} {σ : Subst Γ Δ} {C1 c1} {C2 c2}
  : Tm.substC (@Tm.elimSumC Δ A B M l r t C1 c1) σ (C := C2) (c := c2)
  = (
      @Tm.elimSumC Γ A[σ] B[σ] M[.lift σ]
        (Tm.substC l (.lift σ) (c := .ofEq <| by
          rw [Ty.subst_comp, Ty.subst_comp]
          dsimp [Ty.subst, Subst.cons, lift, wki, wk, var, left, Var.vz, SubstE.wki, Con.ext, Subst.comp]
          congr 1
          grind only [= SubstE.compTS.eq_2, = VarE.subst_vz_lift, = ThinE.wk_id_toSubst, =_ SubstE.compST_wki_lift, = SubstE.comp_id, = SubstE.compTSS_assoc, = ThinE.comp_id, = SubstE.compST_id, =_ SubstE.compSTS_assoc, = ThinE.comp.eq_1, = ThinE.comp_toSubst, = SubstE.compST_toSubst, = TmE.subst.eq_1, =_ SubstE.compRen_wki, = SubstE.compTS_wk_id_cons, = SubstE.compSTS_assoc, =_ ThinE.comp_wk_id, SubstE.lift, = SubstE.compRen_wki, =_ SubstE.compST_toSubst, = SubstE.compTTS_assoc, =_ SubstE.compSTT_assoc, = ThinE.id_toSubst, =_ ThinE.comp_wki_lift_eq_wk, = ThinE.comp.eq_5, = SubstE.comp_wki_lift, = SubstE.compSTT_assoc, =_ SubstE.compTTS_assoc, = SubstE.wki.eq_1, =_ SubstE.comp_toSubst_wk_id, = ThinE.wki_toSubst, = ThinE.id_comp, =_ ThinE.comp_wk_idi_lift_eq_wk, = ThinE.id.eq_2, = ThinE.id_refold, = SubstE.compSST_assoc, =_ ThinE.comp_assoc, = SubstE.comp_wki, =_ ThinE.comp_wki, = ThinE.toSubst.eq_2, = SubstE.comp_assoc, = SubstE.id_compST, SubstE.comp, = SubstE.compTS.eq_3, =_ SubstE.compSST_assoc, = ThinE.comp_assoc, = SubstE.comp_wki_cons, =_ SubstE.comp_wki, = ThinE.comp.eq_4, =_ SubstE.comp_assoc, = VarE.subst.eq_1, = ThinE.lift_toSubst, = ThinE.wk_toSubst, = SubstE.compTS_wki_cons, = SubstE.id_comp, = SubstE.wk.eq_1, = TmE.subst.eq_5, =_ SubstE.compST_wk_id_lift, =_ SubstE.compTSS_assoc, = ThinE.toSubst.eq_3, = SubstE.compTS_toSubst, ThinE.wki]
        ))
        (Tm.substC r (.lift σ) (c := .ofEq <| by
          rw [Ty.subst_comp, Ty.subst_comp]
          dsimp [Ty.subst, Subst.cons, lift, right, wki, wk, var, left, Var.vz, SubstE.wki, Con.ext, Subst.comp]
          congr 1
          grind only [= SubstE.compTS.eq_2, = VarE.subst_vz_lift, = ThinE.wk_id_toSubst, =_ SubstE.compST_wki_lift, = SubstE.comp_id, = SubstE.compTSS_assoc, = ThinE.comp_id, = SubstE.compST_id, =_ SubstE.compSTS_assoc, = ThinE.comp.eq_1, = ThinE.comp_toSubst, = SubstE.compST_toSubst, = TmE.subst.eq_1, =_ SubstE.compRen_wki, = SubstE.compTS_wk_id_cons, = SubstE.compSTS_assoc, =_ ThinE.comp_wk_id, SubstE.lift, = SubstE.compRen_wki, =_ SubstE.compST_toSubst, = SubstE.compTTS_assoc, =_ SubstE.compSTT_assoc, = ThinE.id_toSubst, =_ ThinE.comp_wki_lift_eq_wk, = ThinE.comp.eq_5, = SubstE.comp_wki_lift, = SubstE.compSTT_assoc, =_ SubstE.compTTS_assoc, = SubstE.wki.eq_1, =_ SubstE.comp_toSubst_wk_id, = ThinE.wki_toSubst, = ThinE.id_comp, =_ ThinE.comp_wk_idi_lift_eq_wk, = ThinE.id.eq_2, = ThinE.id_refold, = SubstE.compSST_assoc, =_ ThinE.comp_assoc, = SubstE.comp_wki, =_ ThinE.comp_wki, = ThinE.toSubst.eq_2, = SubstE.comp_assoc, = TmE.subst.eq_6, = SubstE.id_compST, SubstE.comp, = SubstE.compTS.eq_3, =_ SubstE.compSST_assoc, = ThinE.comp_assoc, = SubstE.comp_wki_cons, =_ SubstE.comp_wki, = ThinE.comp.eq_4, =_ SubstE.comp_assoc, = VarE.subst.eq_1, = ThinE.lift_toSubst, = ThinE.wk_toSubst, = SubstE.compTS_wki_cons, = SubstE.id_comp, = SubstE.wk.eq_1, =_ SubstE.compST_wk_id_lift, =_ SubstE.compTSS_assoc, = ThinE.toSubst.eq_3, = SubstE.compTS_toSubst, ThinE.wki]
        ))
        t[σ]
      C2
      (TyConv.ofEq Ty.subst_lift_apply |>.trans (TyConv.subst c1 σ) |>.trans c2)
    )
  := by rfl


end ConvImplicit

theorem Ty.Pi.inj {Γ : Con} {A₁ A₂ : Ty Γ} {B₁ : Ty (Γ.ext A₁)} {B₂ : Ty (Γ.ext A₂)}
  : TyConv (.Pi A₁ B₁) (.Pi A₂ B₂) -> ∃Ac : TyConv A₁ A₂, TyConv B₁ (B₂.conv (ConConv.ext' Ac.symm))
  := by sorry

section HConv
  variable {Γ : Con} {X Y : Ty Γ} {x : Tm Γ X} {y : Tm Γ Y}

  structure TmHConv (x : Tm Γ X) (y : Tm Γ Y) : Prop where
    tyConv : TyConv X Y
    tmConv : TmWConv Γ.2.1 X.1 x.1 y.1

  def TmConv.toTmHConv {x : Tm Γ X} {y : Tm Γ X} (c : TmConv x y) : TmHConv x y where
    tyConv := TyWConv.refl Γ.2.2 X.2
    tmConv := c

  def TmHConv.toTmConv (c : TmHConv x y) : TmConv x (y.conv c.tyConv.symm) := c.tmConv
  -- def TmHConv.toTmConv (c : TmHConv x y) : TmConv x (y.conv h) := c.tmConv -- this is also provable, and is the same statement anyway due to proof irrel

  def TmHConv.refl : @TmHConv Γ X X x x where
    tyConv := .refl
    tmConv := .refl Γ.2.2 X.2 x.2

  def TmHConv.symm (c : TmHConv x y) : @TmHConv Γ Y X y x where
    tyConv := c.tyConv.symm
    tmConv :=
      let res := c.tmConv.symm
      res.conv (.refl Γ) c.tyConv

  def TmHConv.trans {X Y Z} {x y z} (xy : @TmHConv Γ X Y x y) (yz : @TmHConv Γ Y Z y z) : @TmHConv Γ X Z x z where
    tyConv := xy.tyConv.trans yz.tyConv
    tmConv :=
      let tyConv := xy.tyConv.trans yz.tyConv
      let c : TyWConv Γ.2.1 Y.1 X.1 := xy.symm.tyConv
      let res : TmWConv Γ.2.1 X.1 x.1 z.1 := xy.tmConv.trans (yz.tmConv |>.conv (.refl Γ) c)
      res

  def TmConv.toTmHConv_R {x : Tm Γ X} {y : Tm Γ Y} (c : TmConv x (y.conv cTy)) : TmHConv x y where
    tyConv := cTy.symm
    tmConv := c

  def TmConv.toTmHConv_L {x : Tm Γ X} {y : Tm Γ Y} (c : TmConv (x.conv cTy) y) : TmHConv x y :=
    (c.symm |>.toTmHConv_R) |>.symm

  def TmHConv.ofConvTy (x : Tm Γ X) (c : TyConv X Y) : @TmHConv Γ X Y x (x.conv c) where
    tyConv := c
    tmConv := .refl Γ.2.2 X.2 x.2

  def TmHConv.subst {Γ Δ : Con} {X Y : Ty Δ} {x y} (h : @TmHConv Δ X Y x y) (σ : Subst Γ Δ)
    : @TmHConv Γ X[σ] Y[σ] x[σ] y[σ]
    := sorry

  theorem TmHConv.app_subst {Γ Δ A B f a} {σ : Subst Γ Δ}
  : TmHConv (@Tm.app Δ A B f a)[σ] (@Tm.app Γ A[σ] B[.lift σ] f[σ] a[σ])
  where
    tyConv := .ofEq Ty.subst_lift_apply.symm
    tmConv := sorry

end HConv
