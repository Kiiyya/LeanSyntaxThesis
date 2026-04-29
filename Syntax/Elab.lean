import Aesop
import Qq
import Lean
import Syntax.Erased
import Syntax.Wellformed
import Syntax.AllTogether

set_option linter.unusedVariables false

/-
  Elaborator.
  Converts `Lean.Syntax` into `Q(Tm _ _)`.

  Largely based on "What does it take to certify a conversion checker?" by Meven Lennon-Bertrand.
  See the paper at https://arxiv.org/pdf/2502.15500, especially the appendix B.
-/

open Lean Meta Elab Term Qq

def assertDefEq (a b : Expr) (message : MessageData := "") : MetaM Unit := do
  if !(<- Meta.isDefEq a b) then
    throwError "assertDefEq failed {message}:\n{a} is not defeq to {b}"

/-
  # Quotation Helpers
  It is easy to forget what type exacle you're handling when you're just working with `Expr`,
  and Quote4 often misbehaves.
  Hence these helpers, to make life easier.
  These helpers are mostly for documentation.
  They are not rigid, and it is still possible to unsafely cast around,
  since they're just `:= Expr` anyway.
-/

inductive ConQ where
| nil : ConQ
| ext' : ConQ -> Name -> Expr -> ConQ
| unknown : Expr -> ConQ
def TyQ (Γ : ConQ) : Type := Expr
def TmQ (Γ : ConQ) (A : TyQ Γ) : Type := Expr
def VarQ (Γ : ConQ) : Type := Nat
def SubstQ (Γ Δ : ConQ) : Type := Expr
def ConConvQ (Γ Δ : ConQ) : Type := Expr
def TyConvQ {Γ : ConQ} (X Y : TyQ Γ) : Type := Expr
def TmConvQ {Γ : ConQ} {A : TyQ Γ} (x y : TmQ Γ A) : Type := Expr

/-- These two are definitionally equal in our metatheory, i.e. in Lean.
  This is basically Quote4's `_ =Q _`, but behaving a bit better. -/
def TyMDE {Γ : ConQ} (X : TyQ Γ) (Y : TyQ Γ) : Type := Unit

/-- These two are definitionally equal in our metatheory, i.e. in Lean.
  This is basically Quote4's `_ =Q _`, but behaving a bit better.

  If its internal representation is `none`, it means that `X ≡ Y`.
  If its internal representation is `some c`, it means that `c : X ≅ Y`.
  -/
def TmMDE {Γ : ConQ}
  {X : TyQ Γ} {Y : TyQ Γ}
  (x : TmQ Γ X) (y : TmQ Γ Y)
  : Type
  -- := Unit
  := Option (TyConvQ X Y)

@[match_pattern] def ConQ.ext : (Γ : ConQ) -> Name -> TyQ Γ -> ConQ := fun Γ name A => ConQ.ext' Γ name A

def TyQ.unsafeIntro : Expr -> TyQ Γ := id
def TmQ.unsafeIntro : Expr -> TmQ Γ A := id
def VarQ.unsafeIntro : Nat -> VarQ Γ := id
def SubstQ.unsafeIntro : Expr -> SubstQ Γ Δ := id
def ConConvQ.unsafeIntro : Expr -> ConConvQ Γ Δ := id
def TyConvQ.unsafeIntro : Expr -> TyConvQ X Y := id
def TmConvQ.unsafeIntro : Expr -> TmConvQ x y := id
def TyMDE.unsafeIntro : TyMDE X Y := ()
def TmMDE.unsafeIntro : @TmMDE Γ X Y x y := none

def TyQ.unsafeCast : TyQ Γ -> TyQ Γ := id
def TmQ.unsafeCast : TmQ Γ A -> TmQ Γ' A' := id
def VarQ.unsafeCast : VarQ Γ -> VarQ Γ' := id
def SubstQ.unsafeCast : SubstQ Γ Δ -> SubstQ Γ' Δ' := id
def ConConvQ.unsafeCast : ConConvQ Γ Δ -> ConConvQ Γ' Δ' := id
def TyConvQ.unsafeCast : TyConvQ X Y -> TyConvQ X' Y' := id
def TmConvQ.unsafeCast : TmConvQ x y -> TmConvQ x' y' := id
def TmConvQ.unsafeCast! {x : TmQ Γ X} {y : TmQ Γ Y} : @TmConvQ Γ X x y -> TmConvQ x' y' := id

-- def TyConvQ.castR : TyConvQ X Y -> TyMDE Y Z -> TyConvQ X Z := fun a b => a
-- def TyConvQ.castL : TyMDE X Y -> TyConvQ Y Z -> TyConvQ X Z := fun a b => b
-- def TmConvQ.castR : TmConvQ X Y -> TmMDE Y Z -> TmConvQ X Z := fun a b => a
-- def TmConvQ.castL : TmMDE X Y -> TmConvQ Y Z -> TmConvQ X Z := fun a b => b
-- def TmQ.cast : TyMDE A B -> TmQ Γ A -> TmQ Γ B := fun _ t => t

def ConQ.quote : ConQ -> Q(Con)
| .nil => q(Con.nil)
| .ext Γq name Aq =>
  -- let Aq : TyQ Γq := .unsafeIntro Aq
  let Γexpr : Q(Con) := Γq.quote
  .app q(Con.ext $Γexpr) Aq
| .unknown expr => expr
def TyQ.quote {Γ : ConQ} (A : TyQ Γ) : Q(Ty $(Γ.quote)) := A
def TmQ.quote {Γ : ConQ} {A : TyQ Γ} (t : TmQ Γ A) :
  have Γ : Q(Con) := Γ.quote
  have A : Q(Ty $Γ) := A.quote
  Q(Tm $Γ $A)
  := t
def SubstQ.quote (σ : SubstQ Γ Δ) :
  have Γ : Q(Con) := Γ.quote
  have Δ : Q(Con) := Δ.quote
  Q(Subst $Γ $Δ)
  := σ
def ConConvQ.quote (c : ConConvQ Γ Δ) :
  have Γ : Q(Con) := Γ.quote
  have Δ : Q(Con) := Δ.quote
  Q(ConConv $Γ $Δ) := c
def TyConvQ.quote {Γ : ConQ} {X Y : TyQ Γ} (c : TyConvQ X Y) :
  have Γ : Q(Con) := Γ.quote
  have X : Q(Ty $Γ) := X.quote
  have Y : Q(Ty $Γ) := Y.quote
  Q(TyConv $X $Y)
  := c
def TmConvQ.quote {Γ : ConQ} {X : TyQ Γ} {x y : TmQ Γ X} (c : @TmConvQ Γ X x y) :
  have Γ : Q(Con) := Γ.quote
  have X : Q(Ty $Γ) := X.quote
  have x : Q(Tm $Γ $X) := x.quote
  have y : Q(Tm $Γ $X) := y.quote
  Q(TmConv $x $y)
  := c

instance : Coe ConQ Expr where coe Γ := Γ.quote
instance : CoeOut (TyQ Γ) Expr where coe := TyQ.quote
instance : CoeOut (TmQ Γ A) Expr where coe := TmQ.quote
instance : CoeOut (SubstQ Γ Δ) Expr where coe := SubstQ.quote
instance : CoeOut (TyConvQ A B) Expr where coe := TyConvQ.quote
instance : CoeOut (TmConvQ x y) Expr where coe := TmConvQ.quote

def ConConvQ.refl : ConConvQ Γ Γ := .unsafeIntro <| mkAppN q(@ConConv.refl) #[Γ.quote]
def ConConvQ.ext' {X Y : TyQ Γ} (c : TyConvQ X Y) : ConConvQ (.ext Γ x X) (.ext Γ y Y) :=
  mkAppN q(@ConConv.ext') #[Γ.quote, X.quote, Y.quote, c.quote]

def TyQ.U : TyQ Γ := q(@Ty.U $Γ.quote)
def TyQ.El (t : TmQ Γ .U) : TyQ Γ := mkApp2 q(@Ty.El) Γ.quote t.quote
def TyQ.Pi (name : Name) (A : TyQ Γ) (B : TyQ (.ext Γ name A)) : TyQ Γ := mkApp3 q(@Ty.Pi) Γ.quote A.quote B.quote
def TyQ.Unit : TyQ Γ := .app q(@Ty.Unit) Γ.quote
def TyQ.Sum (A B : TyQ Γ) : TyQ Γ := mkApp3 q(@Ty.Sum) Γ.quote A.quote B.quote

def TyQ.subst (A : TyQ Δ) (σ : SubstQ Γ Δ) : TyQ Γ := q(Ty.subst $A.quote $σ.quote)

def SubstQ.apply (a : TmQ Γ A) : SubstQ Γ (.ext Γ name A) :=
  have Γq : Q(Con) := Γ.quote
  have A : Q(Ty $Γq) := A
  let a : Q(Tm $Γq $A) := a
  q(Subst.apply $a)

def SubstQ.comp {Γ Θ Δ : ConQ} (δ : SubstQ Θ Δ) (σ : SubstQ Γ Θ) : SubstQ Γ Δ :=
  have Γ : Q(Con) := Γ.quote
  have Θ : Q(Con) := Θ.quote
  have Δ : Q(Con) := Δ.quote
  have δ : Q(Subst $Θ $Δ) := δ
  have σ : Q(Subst $Γ $Θ) := σ
  q(Subst.comp $δ $σ)

def SubstQ.lift (σ : SubstQ Γ Δ) : SubstQ (Γ.ext name (W.subst σ)) (.ext Δ name W) :=
  have Γq : Q(Con) := Γ.quote
  have Δq : Q(Con) := Δ.quote
  have W : Q(Ty $Δq) := W.quote
  have σ : Q(Subst $Γq $Δq) := σ.quote
  q(@Subst.lift $Γq $Δq $W $σ)

def TmQ.app (f : TmQ Γ (.Pi name A B)) (a : TmQ Γ A) : TmQ Γ (TyQ.subst B (.apply a))
  := mkAppN q(@Tm.app) #[ Γ.quote, A.quote, B.quote, f.quote, a.quote ]

def TmQ.lam {Γ name} {A : TyQ Γ} {B : TyQ (.ext Γ name A)} (body : TmQ (.ext Γ name A) B) : TmQ Γ (TyQ.Pi name A B)
  := mkAppN q(@Tm.lam) #[ Γ.quote, A.quote, B.quote, body.quote ]

def TyQ.conv {Γ Δ : ConQ} (c : ConConvQ Γ Δ) (A : TyQ Γ) : TyQ Δ :=
  mkAppN q(@Ty.conv) #[Γ.quote, Δ.quote, c.quote, A.quote]

def TmQ.conv {Γ : ConQ} {X Y : TyQ Γ} (c : TyConvQ X Y) (t : TmQ Γ X) : TmQ Γ Y :=
  mkAppN q(@Tm.conv) #[Γ.quote, X.quote, Y.quote, c.quote, t.quote]

def ConQ.findVar (n : Name) : (Γ : ConQ) -> Option (VarQ Γ)
| .nil => none
| .ext Γ name _ => if n = name then some .zero else (Γ.findVar n).map Nat.succ
| .unknown expr => none

def VarQ.quote : {Γ : ConQ} -> (v : VarQ Γ) -> Option <| have Γ : Q(Con) := Γ.quote; ((X : Q(Ty $Γ)) × Q(Var $Γ $X))
| .nil                   , v       => none
| .ext Γ name (A : TyQ Γ), .zero   => -- ⊢ `Var (Γ; A) A[wki]`, with `X ≡ A[wki]`
  have Γq : Q(Con) := Γ.quote
  have Aq : Q(Ty $Γq) := @TyQ.quote Γ A
  let Xq : Q(Ty (.ext $Γq $Aq)) := q(Ty.subst $Aq .wki)
  have vq : Q(Var (.ext $Γq $Aq) $Xq) := q(.vz)
  some ⟨Xq, vq⟩
| .ext Γ name (B : TyQ Γ), .succ v => Id.run do -- ⊢ `Var (Γ; B) A[wki]`, with `X ≡ A[wki]`
  have Γq : Q(Con) := Γ.quote
  have B : Q(Ty $Γq) := @TyQ.quote Γ B
  let .some ⟨Y, v⟩ := @VarQ.quote Γ v | return none -- `Y : Ty Γ`, `vq : Var Γ Y`
  have Y : Q(Ty $Γq) := Y
  have v : Q(Var $Γq $Y) := v
  let Ywki : Q(Ty (.ext $Γq $B)) := q(Ty.subst $Y .wki) -- let X : Q(Ty (.ext $Γq $Bq)) := q(@Ty.subst (.ext $Γq $Bq) $Γq $Yq (@Subst.wki $Γq $Bq))
  let vsv : Q(Var (.ext $Γq $B) $Ywki) := q(.vs $v)
  return some ⟨Ywki, vsv⟩
| .unknown _, _ => none

def TyConvQ.refl (X : TyQ Γ) : TyConvQ X X :=
  let Xq := X.quote
  q((TyConv.refl : TyConv $Xq $Xq))

def TyConvQ.symm {X Y : TyQ Γ} (xy : TyConvQ X Y) : TyConvQ Y X :=
  have Xq := X.quote
  have Yq := Y.quote
  have xy : Q(TyConv $Xq $Yq) := xy
  q((TyConv.symm $xy : TyConv $Yq $Xq))

def TyConvQ.trans {X Y Z : TyQ Γ} (xy : TyConvQ X Y) (yz : TyConvQ Y Z) : TyConvQ X Z :=
  have Xq := X.quote
  have Yq := Y.quote
  have Zq := Z.quote
  have xy : Q(TyConv $Xq $Yq) := xy
  have yz : Q(TyConv $Yq $Zq) := yz
  q((TyConv.trans $xy $yz : TyConv $Xq $Zq))

def TyConvQ.ofEq {Γ : ConQ} :
  let Γq := Γ.quote
  {X Y : Q(Ty $Γq)} -> (prf : Q($X = $Y)) -> @TyConvQ Γ X Y
  := @fun X Y prf => q((TyConv.ofEq $prf : TyConv $X $Y))

#check TyConv.Pi
def TyConvQ.Pi {A A' : TyQ Γ}
  {B : TyQ (.ext Γ `anomymous A)}
  {B' : TyQ (.ext Γ `anomymous A')}
  (Ac : TyConvQ A A')
  -- (Bc : @TyConvQ (.ext Γ `anonymous A) B (B'.conv (.ext' Ac.symm)))
  -- (Bc : @TyConvQ (.ext Γ `anonymous A) B B')
  (Bc : Expr)
  : TyConvQ (.Pi `anonymous A B) (.Pi `anonymous A' B')
  := sorry

partial def TyConvQ.isOnlyReflTransSymm (c : TyConvQ X Y) : Bool := go c
  where go (c : Expr) : Bool :=
    match_expr c with
    | TyConv.refl _ _ => true
    | TyConv.trans _ _ _ _ c1 c2 => go c1 && go c2
    | TyConv.symm _ _ _ c => go c
    | _ => false

def TyConvQ.subst (c : @TyConvQ Δ X Y) (σ : SubstQ Γ Δ) : @TyConvQ Γ (X.subst σ) (Y.subst σ) :=
  mkAppN q(@TyConv.subst) #[Δ.quote, Γ.quote, X, Y, c, σ]

#check Ty.subst_comp
#check TyConv.ofEq
def TyConvQ.subst_comp {Γ Θ Δ : ConQ} {A : TyQ Δ} {σ₁ : SubstQ Θ Δ} {σ₂ : SubstQ Γ Θ}
  : TyConvQ ((A.subst σ₁).subst σ₂) (A.subst (σ₁.comp σ₂))
  :=
    let eq := mkAppN q(@Ty.subst_comp) #[Γ.quote, Θ.quote, Δ.quote, A, σ₁, σ₂]
    mkAppN q(@TyConv.ofEq) #[Γ, (A.subst σ₁).subst σ₂, A.subst (σ₁.comp σ₂), eq]

def TmConvQ.refl {X : TyQ Γ} (x : TmQ Γ X) : TmConvQ x x :=
  have Γq := Γ.quote
  have Xq : Q(Ty $Γq) := X.quote
  have xq : Q(Tm $Γq $Xq) := x.quote
  q((TmConv.refl : TmConv $xq $xq))

def TmConvQ.symm {T : TyQ Γ} {x y : TmQ Γ T} (xy : TmConvQ x y) : TmConvQ y x :=
  have Γq := Γ.quote
  have Tq : Q(Ty $Γq) := T.quote
  have xq : Q(Tm $Γq $Tq) := x.quote
  have yq : Q(Tm $Γq $Tq) := y.quote
  have xy : Q(TmConv $xq $yq) := xy
  q((TmConv.symm $xy : TmConv $yq $xq))

def TmConvQ.trans {T : TyQ Γ} {x y z : TmQ Γ T} (xy : TmConvQ x y) (yz : TmConvQ y z) : TmConvQ x z :=
  have Γq : Q(Con) := Γ.quote
  have Tq : Q(Ty $Γq) := T.quote
  have xq : Q(Tm $Γq $Tq) := x.quote
  have yq : Q(Tm $Γq $Tq) := y.quote
  have zq : Q(Tm $Γq $Tq) := z.quote
  have xy : Q(@TmConv $Γq $Tq $xq $yq) := xy
  have yz : Q(@TmConv $Γq $Tq $yq $zq) := yz
  q((TmConv.trans $xy $yz : TmConv $xq $zq))

-- def TmConvQ.ofEq {Γ : ConQ} :
--   let Γq := Γ.quote
--   {X Y : Q(Ty $Γq)} -> (prf : Q($X = $Y)) -> @TyConvQ Γ X Y
--   := @fun X Y prf => q((TyConv.ofEq $prf : TyConv $X $Y))

def TmQ.subst {A : TyQ Δ} (t : TmQ Δ A) (σ : SubstQ Γ Δ) : TmQ Γ (A.subst σ)
  := .unsafeIntro <| mkAppN q(@Tm.subst) #[Γ.quote, Δ.quote, A, t, σ]

#check TyConv.subst_lift_apply
def TyConvQ.subst_lift_apply {σ : SubstQ Γ Δ} {B : TyQ (.ext Δ name A)}
  : TyConvQ
    ((B.subst (.apply a)).subst σ)
    (TyQ.subst (TyQ.subst B (.lift σ)) (.apply (.subst a σ)))
  := .ofEq <| (mkAppN q(@TyConv.subst_lift_apply) #[Γ, Δ, σ, A, B, a] : Expr)

-- def TmHConvQ {Γ : ConQ} {X Y : TyQ Γ} (x : TmQ Γ X) (y : TmQ Γ Y) : Type := Expr
structure TmHConvQ {Γ : ConQ} {X Y : TyQ Γ} (x : TmQ Γ X) (y : TmQ Γ Y) : Type where
  tyConv : TyConvQ X Y
  /-- Do not use this yourself. `TmWConv Γ.2.1 X.1 x.1 y.1` -/
  tmConv :
    have Γ : Q(Con) := Γ.quote
    have X : Q(Ty $Γ) := X.quote
    have Y : Q(Ty $Γ) := Y.quote
    have x : Q(Tm $Γ $X) := x.quote
    have y : Q(Tm $Γ $Y) := y.quote
    Q(TmWConv $Γ.2.1 $X.1 $x.1 $y.1)

def TmHConvQ.ofExpr (expr : Expr) : @TmHConvQ Γ X Y x y :=
  let tyConv := mkAppN q(@TmHConv.tyConv) #[Γ, X, Y, x, y, expr]
  let tmConv := mkAppN q(@TmHConv.tmConv) #[Γ, X, Y, x, y, expr]
  ⟨tyConv, tmConv⟩

def TmHConvQ.unsafeCast (h : TmHConvQ x y) : TmHConvQ x' y' where
  tyConv := h.tyConv
  tmConv := h.tmConv

def TmHConvQ.ofTmConvQ (c : TmConvQ x y) : TmHConvQ x y where
  tyConv := .refl _
  tmConv := c

def TmHConvQ.quote {X Y : TyQ Γ} {x : TmQ Γ X} {y : TmQ Γ Y} (h : TmHConvQ x y) : Expr
  := mkAppN q(@TmHConv.mk) #[Γ.quote, X, Y, x, y, h.tyConv, h.tmConv]

-- def TmHConvQ.toTyConvQ (c : @TmHConvQ Γ X Y x y) : TyConvQ X Y :=
--   sorry

def TmHConvQ.refl (x : TmQ Γ X) : TmHConvQ x x where
  tyConv := .refl X
  tmConv := TmConvQ.refl x

def TmHConvQ.symm (xy : @TmHConvQ Γ X Y x y) : TmHConvQ y x :=
  let tyConv := xy.tyConv.symm
  -- have Γ : Q(Con) := Γ.quote
  -- have X : Q(Ty $Γ) := X.quote
  -- have Y : Q(Ty $Γ) := Y.quote
  -- have x : Q(Tm $Γ $X) := x.quote
  -- have y : Q(Tm $Γ $Y) := y.quote
  let tmp := mkAppN q(@TmHConv.symm) #[Γ, X, Y, x, y, xy.quote] -- very inefficient, but for now, whatever
  let tmp := mkAppN q(@TmHConv.tmConv) #[Γ, X, Y, x, y, tmp]
  ⟨tyConv, tmp⟩

def TmHConvQ.trans (xy : @TmHConvQ Γ X Y x y) (yz : @TmHConvQ Γ Y Z y z) : TmHConvQ x z :=
  let tyConv := xy.tyConv |>.trans yz.tyConv
  let tmp := mkAppN q(@TmHConv.trans) #[Γ, X, Y, Z, x, y, z, xy.quote, yz.quote] -- very inefficient...
  let tmp := mkAppN q(@TmHConv.tmConv) #[Γ, X, Z, x, z, tmp]
  ⟨tyConv, tmp⟩

#check TmHConv.ofConvTy
def TmHConvQ.ofConvTy (x : TmQ Γ X) (c : TyConvQ X Y) : @TmHConvQ Γ X Y x (x.conv c) where
  tyConv := c
  tmConv :=
    -- see `TmHConv.ofConvTy` for a justification
    have Γ : Q(Con) := Γ.quote
    have X : Q(Ty $Γ) := X
    have x : Q(Tm $Γ $X) := x
    (mkAppN q(@TmConv.refl) #[q($Γ.2.2), q($X.2), q($x.2)] : Expr)

def TmHConvQ.subst (h : @TmHConvQ Δ X Y x y) (σ : SubstQ Γ Δ)
    : @TmHConvQ Γ _ _ (x.subst σ) (y.subst σ)
    :=
      let tmp := mkAppN q(@TmHConv.subst) #[Γ, Δ, X, Y, x, y, h.quote, σ]
      let tyConv := mkAppN q(@TmHConv.tyConv) #[Γ, X.subst σ, Y.subst σ, x.subst σ, y.subst σ, tmp]
      let tmConv := mkAppN q(@TmHConv.tmConv) #[Γ, X.subst σ, Y.subst σ, x.subst σ, y.subst σ, tmp]
      ⟨tyConv, tmConv⟩

def TmHConvQ.app_subst {Γ Δ A B f a} {σ : SubstQ Γ Δ}
  : TmHConvQ (.subst (@TmQ.app Δ name A B f a) σ) (@TmQ.app Γ name (A.subst σ) (B.subst (.lift σ)) (f.subst σ) (a.subst σ))
  :=
    let tmp := mkAppN q(@TmHConv.app_subst) #[Γ, Δ, A, B, f, a, σ]
    let args : Array Expr := #[Γ,
        ((B.subst (.apply a)).subst σ),
        ((B.subst σ.lift).subst (.apply (a.subst σ))),
        ((f.app a).subst σ),
        ((f.subst σ).app (B := B) (a.subst σ))
      ]
    let tyConv := mkAppN q(@TmHConv.tyConv) args
    let tmConv := mkAppN q(@TmHConv.tmConv) args
    ⟨tyConv, tmConv⟩

attribute [irreducible] TyQ
attribute [irreducible] TmQ
attribute [irreducible] VarQ
attribute [irreducible] SubstQ
attribute [irreducible] ConConvQ
attribute [irreducible] TyConvQ
attribute [irreducible] TmConvQ
attribute [irreducible] TyMDE
attribute [irreducible] TmMDE

structure IsPiResult (T : TyQ Γ) where
  name : Name := `anonymous
  A : TyQ Γ
  B : TyQ (.ext Γ name A)
  conv : TyConvQ T (TyQ.Pi name A B)

partial def TyQ.isPi {Γ : ConQ} (T : TyQ Γ) : MetaM <| Option (IsPiResult T) := do
  match_expr T with
  | Ty.Pi Γ_ A B =>
    have A : TyQ Γ := .unsafeIntro A
    have B : TyQ (.ext Γ `anonymous A) := .unsafeIntro B
    return some { A, B, conv := (TyConvQ.refl T).unsafeCast }
  | Ty.conv _ _ _ _ => -- todo look through conv
    throwError "TyQ.isPi: not impl for Ty.conv yet"
  | _ => return none

structure IsElResult (T : TyQ Γ) where
  t : TmQ Γ .U
  conv : TyConvQ T (TyQ.El t)

partial def TyQ.isEl {Γ : ConQ} (T : TyQ Γ) : MetaM <| Option (IsElResult T) := do
  match_expr T with
  | Ty.El Γ_ t =>
    have t : TmQ Γ .U := .unsafeIntro t
    return some { t, conv := (TyConvQ.refl T).unsafeCast }
  | Ty.conv _ _ _ _ => -- todo look through conv
    throwError "TyQ.isEl: not impl for Ty.conv yet"
  | _ => return none

structure IsUResult (T : TyQ Γ) where
  conv : TyConvQ T .U

partial def TyQ.isU {Γ : ConQ} (T : TyQ Γ) : MetaM <| Option (IsUResult T) := do
  match_expr T with
  | Ty.U Γ_ =>
    return some { conv := (TyConvQ.refl T).unsafeCast }
  | Ty.conv _ _ _ _ => -- todo look through conv
    throwError "TyQ.isU: not impl for Ty.conv yet"
  | _ => return none

structure IsAppResult (t : TmQ Γ T) where
  name : Name := `anonymous
  A : TyQ Γ
  B : TyQ (.ext Γ name A)
  f : TmQ Γ (.Pi name A B)
  a : TmQ Γ A
  conv : TmHConvQ t (.app f a)
  -- mde : @TmMDE Γ T (TyQ.subst B (.apply a)) t (.app f a)
  -- Conv : TyConvQ T (TyQ.subst B (.apply a))
  -- -- conv : @TmConvQ Γ T t ((TmQ.app f a).conv Conv.symm) -- maybe use TmHConvQ?
  -- conv : @TmConvQ Γ (TyQ.subst B (.apply a)) (t.conv Conv) (TmQ.app f a) -- maybe use TmHConvQ?
partial def TmQ.isApp {Γ : ConQ} {T : TyQ Γ} (t : TmQ Γ T) : MetaM <| Option (IsAppResult t) := do
  match_expr t with
  | Tm.app _ A B f a =>
    let A : TyQ Γ := .unsafeIntro A
    let B : TyQ (.ext Γ `anonymous A) := .unsafeIntro B
    let f : TmQ Γ (.Pi `anonymous A B) := .unsafeIntro f
    let a : TmQ Γ A := .unsafeIntro a
    -- have A : Q(Ty $Γ_) := A
    -- have B : Q(Ty (.ext $Γ_ $A)) := B
    -- have f : Q(Tm $Γ_ (.Pi $A $B)) := f
    -- have a : Q(Tm $Γ_ $A) := a
    -- have _prf : $T_ =Q Ty.subst $B (.apply $a) := .unsafeIntro
    -- have _prf : $t_ =Q .app $f $a := .unsafeIntro
    -- let tmConv : Q(TmWConv $Γ_.2.1 $T_.1 $t_.1 (.app $A.1 $B.1 $f.1 $a.1)) := q(.refl $Γ_.2.2 $T_.2 $t_.2)
    -- let conv : TmHConvQ t (.app f a) := ⟨q(@TyConv.refl $Γ_ $T_), tmConv⟩
    -- let Conv : TyConvQ T (TyQ.subst B (SubstQ.apply a)) := q(@TyConv.refl $Γ_ $T_)

    let T_conv_Ba : TyConvQ T (TyQ.subst B (SubstQ.apply a)) := (TyConvQ.refl T).unsafeCast -- okay because `T ≡ B[a]` is defeq -- todo assign T.
    -- todo: move the below line for `e : Expr` somewhere else
    let e : Expr := TmConvQ.refl t |>.quote -- okay because `T ≡ B[a]` defeq and because `t ≡ .app f a` also defeq
    let conv : @TmHConvQ Γ T (B.subst (SubstQ.apply a)) t (f.app a) := ⟨T_conv_Ba, e⟩
    return some { A, B, f, a, conv }

  | Tm.conv _ X _T X_conv_T t' =>
    have X : TyQ Γ := .unsafeIntro X
    have t' : TmQ Γ X := .unsafeIntro t'
    have X_conv_T : TyConvQ X T := .unsafeIntro X_conv_T
    let some ⟨name, A, B, f, a, conv⟩ <- TmQ.isApp t' | return none
    let Conv : TyConvQ T (TyQ.subst B (.apply a)) := .trans X_conv_T.symm conv.tyConv
    let h1 := TmHConvQ.ofConvTy t' X_conv_T |>.symm
    let conv : @TmHConvQ Γ T (B.subst (SubstQ.apply a)) (t'.conv X_conv_T) (f.app a) := h1.trans conv
    let conv : @TmHConvQ Γ T (B.subst (SubstQ.apply a)) t (f.app a) := conv.unsafeCast -- okay because `t ≡ t'.conv _` is a defeq
    return some {
      name := name
      A := A
      B := B
      f := f
      a := a
      conv
    }
  -- | Tm.subst .. => or maybe just handle this elsewhere
  | _ => return none

structure IsLamResult (t : TmQ Γ T) where
  name : Name := `anonymous
  A : TyQ Γ
  B : TyQ (.ext Γ name A)
  body : TmQ (.ext Γ name A) B
  Conv : TyConvQ T (.Pi name A B)

partial def TmQ.isLam {Γ : ConQ} {T : TyQ Γ} (t : TmQ Γ T) : MetaM <| Option (IsLamResult t) := do
  match_expr t with
  | Tm.lam _ A B body =>
    let A : TyQ Γ := .unsafeIntro A
    let B : TyQ (.ext Γ `anonymous A) := .unsafeIntro B
    let body : TmQ (.ext Γ `anonymous A) B := .unsafeIntro body
    let Conv : TyConvQ T (TyQ.Pi `anonymous A B) := .unsafeCast (.refl T) -- okay because this is a defeq
    return some { A, B, body, Conv }
  | Tm.conv _ X __T X_conv_T t' =>
    have X : TyQ Γ := .unsafeIntro X
    have t' : TmQ Γ X := .unsafeIntro t'
    have X_conv_T : TyConvQ X T := .unsafeIntro X_conv_T
    let some {name, A, B, body, Conv := X_conv_PiAB } <- TmQ.isLam t' | return none
    let T_conv_PiAB : TyConvQ T (.Pi name A B) := .trans X_conv_T.symm X_conv_PiAB
    return some {
      name
      A
      B
      body
      Conv := T_conv_PiAB
    }
  -- | Tm.subst .. => or maybe just handle this elsewhere
  | _ => return none

structure IsSubstTyResult (Y : TyQ Γ) where
  Δ : ConQ
  X : TyQ Δ
  σ : SubstQ Γ Δ
  conv : TyConvQ Y (X.subst σ)

partial def TyQ.isSubst {Γ : ConQ} {Y : TyQ Γ} : MetaM <| Option (IsSubstTyResult Y) :=
  match_expr Y with
  | Ty.subst _ Δ X σ =>
    let Δ : ConQ := .unknown Δ
    let X : TyQ Δ := .unsafeIntro X
    let σ : SubstQ Γ Δ := .unsafeIntro σ
    return some { Δ, X, σ, conv := (TyConvQ.refl Y).unsafeCast } -- okay because defeq
  -- todo look through conv
  | _ => return none

structure IsSubstTmResult (y : TmQ Γ Aσ) where
  Δ : ConQ
  A : TyQ Δ
  x : TmQ Δ A
  σ : SubstQ Γ Δ
  -- Conv : TyConvQ Aσ (TyQ.subst A σ)
  conv : TmHConvQ y (TmQ.subst x σ)

partial def TmQ.isSubst {Γ : ConQ} {Aσ : TyQ Γ} {y : TmQ Γ Aσ} : MetaM <| Option (IsSubstTmResult y) :=
  match_expr y with
  | Tm.subst _ Δ A x σ =>
    let Δ : ConQ := .unknown Δ
    let A : TyQ Δ := .unsafeIntro A
    let x : TmQ Δ A := .unsafeIntro x
    let σ : SubstQ Γ Δ := .unsafeIntro σ
    return some { Δ, A, σ, x, conv := (TmHConvQ.refl y).unsafeCast }
  -- todo look through conv
  | _ => return none

/-
  # Reduction

  For now, we use Quote4's `| ~q(..) => ...` to match on expressions, but this is overkill and
  has performance issues. I worry it might accidentally unfold too much while checking defeq.
  Instead, `match_expr` would be more performant and would not unfold exprs, but also a pain to write.

  It might also be helpful to have a dedicated reduction relation, instead of piggybacking on TyConv.

  We also reduce away substitutions as far as possible.
-/

-- partial def TmE.redM {γ : Q(Nat)} (t : Q(TmE $γ)) : MetaM ((t' : Q(TmE $γ)) × Q(TmERed $t $t')) := do
--   -- withTraceNode `stx.red (myLog (f_err := fun err => return m!"TmE.red {t} ~~> ERROR {err.toMessageData}") (fun ⟨t', prf⟩ => return m!"TmE.red {t} ~~> {t'}\nProof: {prf}")) do
--   -- withTraceNode `stx.red (niceLog m!"TmE.redM {t}") do
--   let t₂ : Q(TmE $γ) <- whnf t
--   have : $t =Q $t₂ := .unsafeIntro
--   match t₂ with
--   | ~q(TmE.app $A $B $f $a) =>
--     let f₂ : Q(TmE $γ) <- whnf f
--     have : $f =Q $f₂ := .unsafeIntro
--     match f₂ with
--     | ~q(TmE.lam $A' $B' $body) => -- have `(λ. body) a`, reduce to `body[a]`
--       let t' : Q(TmE $γ) := q(TmE.subst $body (.cons .id $a))
--       -- return ⟨q($t'), q(TmERed.beta)⟩
--       let ⟨t'', prf⟩ <- TmE.redM q($t')
--       return ⟨q($t''), q(TmERed.trans TmERed.beta $prf)⟩
--     | _ => -- `f a ~~> f' a`
--       let ⟨f', red⟩ <- TmE.redM q($f₂)
--       return ⟨q(.app $A $B $f' $a), q(TmERed.app $red)⟩
--   | _ => return ⟨t, q(.refl)⟩

#check Tm.app_subst
#check TmConv.beta
#check Ty.Pi_subst


mutual
  -- Ignore the extra return type `Y` if it confuses you. Reduction works on preterms in the paper anyway.
  partial def TmQ.red {Γ : ConQ} {X : TyQ Γ} (x : TmQ Γ X) : MetaM <| (Y : TyQ Γ) × (y : TmQ Γ Y) × TmHConvQ x y := do
    let cont {Y} (y : TmQ Γ Y) (x_red_y : TmHConvQ x y) : MetaM <| (Z : TyQ Γ) × (z : TmQ Γ Z) × TmHConvQ x z := do
      let ⟨Z, z, y_red_z⟩ <- TmQ.red y
      let x_red_z := TmHConvQ.trans (Γ := Γ) (x := x) x_red_y y_red_z
      return ⟨Z, z, x_red_z⟩
    if let .some ⟨Δ, C, t, σ, x_conv_tσ⟩ <- x.isSubst then
      -- `x ≡ t[σ] : C[σ]` with `T ≡ C[σ]`
      -- let x_mde : TmMDE x (TmQ.subst t σ) := .unsafeIntro
      if let .some ⟨name, A, B, f, a, t_conv_app⟩ <- t.isApp then
        -- `t ≡ .app f a` of type `B[apply a]`
        -- `x ≡ (.app f a)[σ]` of type `B[apply a][σ]`
        -- with Conv : `C ≅ B[apply a]`
        let Aσ := TyQ.subst A σ
        let Bσ := TyQ.subst B σ.lift
        let fσ : TmQ Γ ((TyQ.Pi name A B).subst σ) := TmQ.subst f σ
        let fσ : TmQ Γ (TyQ.Pi name (A.subst σ) (B.subst σ.lift)) := fσ.unsafeCast -- okay because `(Pi A B)[σ] ≡ Pi A[σ] B[lift σ]` is a defeq, see `Ty.Pi_subst`
        let aσ := TmQ.subst a σ

        let Y := TyQ.subst (TyQ.subst B (.lift σ)) (.apply (.subst a σ))
        let y : TmQ Γ Y := .app fσ aσ -- `.app f[σ] a[σ]` of type `B[lift σ][apply a[σ]]`

        let prf := t_conv_app.subst σ -- `t[σ] ≅ (app f a)[σ]`
        let prf := x_conv_tσ |>.trans prf -- `x ≅ (app f a)[σ]`
        let prf := prf |>.trans TmHConvQ.app_subst

        return <- cont y prf
    return ⟨X, x, .refl x⟩
    -- sorry
    -- match_expr x with -- `Γ ⊢ x : T`
    -- | Tm.subst _ Δ C t σ =>
    --   -- `Γ ⊢ t[σ] : C[σ]` with `T ≡ C[σ]` and `x ≡ t[σ]`, with `Δ ⊢ t : C`
    --   have Δ : ConQ := .unknown Δ
    --   have C : TyQ Δ := .unsafeIntro C
    --   have t : TmQ Δ C := .unsafeIntro t
    --   have σ : SubstQ Γ Δ := .unsafeIntro σ
    --   match_expr t with -- `Δ ⊢ t : C`
    --   | Tm.app _ A B f a => -- ** `(f a)[σ] = (f[σ] a[σ])` : `B[lift σ][apply a[σ]]` by Tm.app_subst
    --     -- ? problem: `B[apply a][σ]` is only propEq to `B[lift σ][apply a[σ]]`, not defeq in metatheory.
    --     -- `Δ ⊢ (f a) : B[apply a]` with `C ≡ B[apply a]`
    --     have A : Q(Ty $Δ) := A
    --     have B : Q(Ty (.ext $Δ $A)) := B
    --     have f : Q(Tm $Δ (.Pi $A $B)) := f
    --     have a : Q(Tm $Δ $A) := a
    --     have Aσ : Q(Ty $Γ_) := q(Ty.subst $A $σ)
    --     have _prf : $Aσ =Q (Ty.subst $A $σ) := .unsafeIntro
    --     have Bσ : Q(Ty (.ext $Γ_ $Aσ)) := q(Ty.subst $B (Subst.lift (W := $A) $σ))
    --     have _prf : $Bσ =Q Ty.subst $B (Subst.lift (W := $A) $σ) := .unsafeIntro
    --     have fσ : Q(Tm $Γ_ (.Pi $Aσ $Bσ)) := q(Tm.subst $f $σ)
    --     have aσ : Q(Tm $Γ_ $Aσ) := q(Tm.subst $a $σ)
    --     have x : Q(Tm $Γ_ (Ty.subst (Ty.subst $B (.apply $a)) $σ)) := x
    --     have y : Q(Tm $Γ_ (Ty.subst $Bσ (.apply $aσ))) := q(@Tm.app $Γ_ $Aσ $Bσ $fσ $aσ)
    --     have typeConv : Q(TyConv (Ty.subst $Bσ (.apply $aσ)) (Ty.subst (Ty.subst $B (.apply $a)) $σ) )
    --       := q(.ofEq sorry) -- todo
    --     have y : Q(Tm $Γ_ (Ty.subst (Ty.subst $B (.apply $a)) $σ)) := q(Tm.conv $typeConv $y)
    --     have x_red_y : Q(TmConv $x $y)
    --       -- := q(TmConv.ofEq Tm.app_subst) -- todo
    --       := q(sorry)
    --     cont y x_red_y
    --   | _ => return ⟨x, .refl x⟩
    -- | Tm.app _ A B f a =>
    --   -- `Γ ⊢ f a : B[apply a]` with `T ≡ B[apply a]`
    --   have A : Q(Ty $Γ_) := A
    --   have B : Q(Ty (.ext $Γ_ $A)) := B
    --   have f : Q(Tm $Γ_ (.Pi $A $B)) := f
    --   have a : Q(Tm $Γ_ $A) := a
    --   have _prf : $T_ =Q Ty.subst $B (.apply $a) := .unsafeIntro
    --   match_expr f with
    --   | Tm.lam _ _A _B body => -- ** beta reduction: `Γ ⊢ .app (.lam body) a ≅ body[apply a] : B[apply a]`
    --     have body : Q(Tm (.ext $Γ_ $A) $B) := body
    --     let y : Q(Tm $Γ_ (Ty.subst $B (.apply $a))) := q(Tm.subst $body (.apply $a))
    --     let x_red_y : Q(TmConv (.app (.lam $body) $a) $y) := q(TmConv.beta $body $a)
    --     cont y x_red_y
    --   | _ => return ⟨x, .refl x⟩
    -- | _ => return ⟨x, .refl x⟩

  partial def TyQ.red {Γ : ConQ} (X : TyQ Γ) : MetaM <| (Y : TyQ Γ) × TyConvQ X Y := do
    let cont (Y : TyQ Γ) (X_red_Y : TyConvQ X Y) : MetaM <| (Z : TyQ Γ) × TyConvQ X Z := do
      let ⟨Z, Y_red_Z⟩ <- TyQ.red Y
      let X_red_Z := TyConvQ.trans (X := X) X_red_Y Y_red_Z
      return ⟨Z, X_red_Z⟩

    if let some ⟨Θ, X', σ1, conv⟩ <- X.isSubst then
      if let some ⟨Δ, X'', σ2, conv₂⟩ <- X'.isSubst then
        -- `X''[σ2][σ1] = X''[σ2 ∘ σ1]`
        let σ := SubstQ.comp σ2 σ1
        let Y := TyQ.subst X'' σ
        have prf : @TyConvQ Γ ((X''.subst σ2).subst σ1) Y := .subst_comp
        have tmp := conv₂.subst σ1
        have tmp := conv.trans tmp
        return <- cont Y (tmp.trans prf)

    if let some ⟨Δ, X', σ, conv1⟩ <- X.isSubst then
      if let some ⟨conv2⟩ <- X'.isU then
        let Y := @TyQ.U Γ -- `U[σ] ≡ U`
        return <- cont TyQ.U sorry
      if let some ⟨name, A, B, conv⟩ <- X'.isPi then
        sorry
      if let some ⟨t, conv⟩ <- X'.isEl then
        let y : TmQ Γ (.subst .U σ) := t.subst σ
        let y : TmQ Γ .U := y.unsafeCast -- okay because this is a defeq
        return ⟨TyQ.El y, sorry⟩

    return ⟨X, .refl X⟩

    -- have Γq : Q(Con) := Γ.quote
    -- have Xq : Q(Ty $Γq) := X
    -- let cont (Y : TyQ Γ) (X_red_Y : TyConvQ X Y) : MetaM <| (Z : TyQ Γ) × TyConvQ X Z := do
    --   let ⟨Z, Y_red_Z⟩ <- TyQ.red Y
    --   let X_red_Z := TyConvQ.trans (X := X) X_red_Y Y_red_Z
    --   return ⟨Z, X_red_Z⟩
    -- match Xq with
    -- | ~q(Ty.subst (Ty.subst $A $σ1) $σ2) => -- `A[σ1][σ2] = A[σ1 ∘ σ2]`
    --   let Y : Q(Ty $Γq) := q(Ty.subst $A (Subst.comp $σ1 $σ2))
    --   let X_red_Y : Q(TyConv $Xq $Y) := q(TyConv.ofEq Ty.subst_comp)
    --   cont Y X_red_Y
    -- | ~q(Ty.subst .U $σ) => -- `U[σ] ≡ U`
    --   let Y : Q(Ty $Γq) := q(.U)
    --   return ⟨Y, .refl X⟩
    -- | ~q(Ty.subst (.El $t) $σ) => -- `(.El t)[σ] ≡ El t[σ]` (todo: insert ofEq proof anyway, to help lean unifier?)
    --   let Y : Q(Ty $Γq) := q(Ty.El (Tm.subst $t $σ))
    --   cont Y (.refl X)
    -- | ~q(Ty.subst (.Pi $A $B) $σ) => -- `(.Pi A B)[σ] ≡ Pi A[σ] B[lift σ]`
    --   let Y : Q(Ty $Γq) := q(Ty.Pi (.subst $A $σ) (Ty.subst $B (.lift $σ)))
    --   cont Y (.refl X)
    -- | _ => return ⟨Xq, .refl X⟩ -- no-op


  /- The Quote4 match arms above do something like this, iirc:
    let Δ : Q(Con) <- mkFreshExprMVarQ q(Con)
    let A : Q(Ty $Δ) <- mkFreshExprMVarQ q(Ty $Δ)
    let B : Q(Ty (.ext $Δ $A)) <- mkFreshExprMVarQ q(Ty (.ext $Δ $A))
    let σ : Q(Subst $Γq $Δ) <- mkFreshExprMVarQ q(Ty (.ext $Δ $A))
    if let .defEq _prf <- isDefEqQ q(Ty.subst (.Pi $A $B) $σ) q($Xq) then
      let e : Q(Ty $Γq) := q(Ty.Pi (Ty.subst $A $σ) (Ty.subst $B (.lift $σ)))
      sorry
    else sorry
  -/

  /- This would be more efficient, but very painful to write:
    match_expr X with
    | Ty.subst Γ Δ Y σ =>
      match_expr Y with
      | Ty.Pi Δ A B => -- `(Pi A B)[σ] ≡ Pi A[σ] [lift σ]` by rfl
        let Aσ := mkApp4 q(@Ty.subst) Γ Δ A σ
        let e :=
          mkApp3 q(@Ty.Pi)
            Γ
            (mkApp4 q(@Ty.subst) Γ Δ A σ)
            (mkApp4 q(@Ty.subst)
              (mkApp2 q(@Con.ext) Γ Aσ)
              (mkApp2 q(@Con.ext) Δ A)
              B
              (mkAppN q(@Subst.lift) #[Γ, Δ, A, σ]))
        return ⟨e, @TyConvQ.refl Γ e⟩ -- defeq, so just by rfl
      | _ => sorry
    | _ => sorry
  -/
end

/-
  # Typed Algorithmic Conversion Checking
-/

-- /-- Strips `Ty.conv`s.
--   Given a `Ty.conv c X : Ty Γ`, return just `X : Ty Δ` for some other context.
--   We still pretend that we return `X : Ty Γ`, which is wrong! But, in `Ty.isDefEqRed` we ignore
--   contexts, and so this is okay.
--   Due to `c : Γ ≅ Δ` we still have `Ty Γ = Ty Δ`, but since Lean is an intensional type theory,
--   we need the conversion cast.
-- -/
-- private partial def TyQ.stripConv (X : TyQ Γ) : TyQ Γ :=
--   match_expr X with
--   | Ty.conv _ _ _ X => TyQ.stripConv X
--   | _ => X
-- private partial def TmQ.stripConv (t : TmQ Γ X) : TmQ Γ X :=
--   match_expr t with
--   | Tm.conv _ _ _ _ t => TmQ.stripConv t
--   | _ => t

#check TmWConv.app

structure TmQ.InferRedResult (x : TmQ Γ X) (y : TmQ Γ Y) where
  /-- The inferred pre-reduced type. -/
  T : TyQ Γ
  T_conv_X : TyConvQ T X
  T_conv_Y : TyConvQ T Y
  conv : TmHConvQ x y

structure TmQ.InferResult (x : TmQ Γ X) (y : TmQ Γ Y) where
  conv : TmHConvQ x y

#check Ty.Pi.inj
def TyQ.Pi_inj (c : @TyConvQ Γ (.Pi a1 A₁ B₁) (.Pi a2 A₂ B₂))
  : (Ac : @TyConvQ Γ A₁ A₂) × @TyConvQ (.ext Γ a1 A₁) B₁ (B₂.conv (ConConvQ.ext' Ac.symm))
  := sorry

mutual
  -- /-- `Γ ⊢ t ~ₕ t' |> T` Neutral terms are comparable, inferring the *reduced* type T.
  --   The `out_T` here is an output, and should be a metavariable. -/
  -- partial def TmQ.inferRed (out_T : TyQ Γ) (x y : TmQ Γ out_T) : MetaM (TmHConvQ x y) := do
  --   throwError "TmQ.inferRed: not yet implemented"

  /-- `Γ ⊢ t ~ₕ t' |> T` Neutral terms are comparable, inferring the *reduced* type T. -/
  -- partial def TmQ.inferRed (x : TmQ Γ out_X) (y : TmQ Γ out_Y) : MetaM (@TmHConvQ Γ out_X out_Y x y) := do
  partial def TmQ.inferRed (x : TmQ Γ out_X) (y : TmQ Γ out_Y) : MetaM (TmQ.InferRedResult x y) := do
    throwError "TmQ.inferRed: not yet implemented"

  -- /-- `Γ ⊢ t ~ t' |> T` Neutral terms are comparable, inferring type T.
  --   The `out_T` here is an output, and should be a metavariable. -/
  -- partial def TmQ.infer (out_T : TyQ Γ) (x y : TmQ Γ out_T) : MetaM (TmHConvQ x y) := do

  /-- `Γ ⊢ x ~ y |> X` Neutral terms are comparable, inferring type X. -/
  partial def TmQ.infer (x : TmQ Γ out_X) (y : TmQ Γ out_Y) : MetaM (TmHConvQ x y) := do
    have Γq : Q(Con) := Γ.quote
    if let some ⟨name1, A1, B1, n, u, Conv⟩ <- x.isApp then
      if let .some ⟨name2, A2, B2, n', u', Conv'⟩ <- y.isApp then
        -- __NApp__
        let ⟨T, T_conv_idk, T_conv_idk2, conv⟩ <- TmQ.inferRed n n'
        let some ⟨name, A, B, T_conv_PiAB⟩ <- T.isPi | throwError "TmQ.infer: NApp case, inferRed returned {T.quote} which is not a Pi"
        let A1c : TyConvQ A1 A := sorry
        let A2c : TyConvQ A2 A := sorry
        let B1c : TyConvQ B1 (B.conv (.ext' A1c.symm)) := sorry
        let B2c : TyConvQ B2 (B.conv (.ext' A2c.symm)) := sorry
        -- let n : TmQ Γ (.Pi name A B) := n.unsafeCast
        -- let n' : TmQ Γ (.Pi name A B) := n'.unsafeCast
        -- let u : TmQ Γ A := u.unsafeCast
        -- let u' : TmQ Γ A := u'.unsafeCast

        let u_conv_u' <- TmQ.isDefEq A (u.conv A1c) (u'.conv A2c)
        let .true <- Meta.isDefEq out_T (TyQ.subst B (.apply u)) | throwError "TmQ.infer: Failed to assign {out_T.quote}" -- assign `out_T` := `B[u]`
        let prf : TmConvQ x y := q((sorry : @TmConv $Γq ))
        return sorry
    throwError "{Expr.const `TmQ.infer []}: Don't know how to handle\n  {x.quote}\n~\n  {y.quote}\n|>\n  {out_T.quote}"

  -- partial def TmE.isDefEqM {γ : Q(Nat)} (Γ : Q(ConE $γ)) (X : Q(TyE $γ)) (x₁ x₂ : Q(TmE $γ)) : MetaM Q(TmEDefEq $Γ $X $x₁ $x₂) := do
  --   -- withTraceNode `stx.isDefEq (niceLog m!"TmE.isDefEqM (X:={X}): checking\n  {x₁}\n≅ {x₂}\n") do
  --   let ⟨X', X_red⟩ <- TyE.redM X
  --   let ⟨x₁', x₁_red⟩ <- TmE.redM x₁
  --   let ⟨x₂', x₂_red⟩ <- TmE.redM x₂
  --   match X' with
  --   | ~q(.Pi $A $B) => -- __negative__: Want `Γ ⊢ x₁ ≅ₕ x₂ : Pi A B`, so do η-expansion
  --     let x_eta : Q(TmE ($γ + 1)) := q(TmE.app (TyE.subst $A .wki) (TyE.subst $B (.lift .wki)) (TmE.subst $x₁' .wki) (.var .vz))
  --     let y_eta : Q(TmE ($γ + 1)) := q(TmE.app (TyE.subst $A .wki) (TyE.subst $B (.lift .wki)) (TmE.subst $x₂' .wki) (.var .vz))
  --     let prf   : Q(TmEDefEq (.ext $Γ $A) $B $x_eta $y_eta) <- TmE.isDefEqM q(.ext $Γ $A) q($B) q($x_eta) q($y_eta)
  --     let prf'  : Q(TmEDefEq $Γ (.Pi $A $B) $x₁' $x₂') := q(TmEDefEq.eta $prf)
  --     let prf'' : Q(TmEDefEq $Γ $X $x₁ $x₂) := q(TmEDefEq.red_cert $X_red $x₁_red $x₂_red $prf')
  --     return prf''
  --   | ~q(.U) =>
  --     match x₁', x₂' with
  --     | ~q(.pi $A $B), ~q(.pi $A' $B') => -- __positive-canonical__: Want `Γ ⊢ Pi A B ≅ₕ Pi A' B' : U`, so use Pi-congr
  --       let A_defeq_A' <- TmE.isDefEqM Γ q(.U) q($A) A'
  --       let B_defeq_B' <- TmE.isDefEqM q(.ext $Γ $A) q(.U) B B'
  --       let prf := q(TmEDefEq.congr_pi $A_defeq_A' $B_defeq_B')
  --       return q(TmEDefEq.red_cert $X_red $x₁_red $x₂_red $prf)
  --     | _, _ => -- __positive-neutral__: From `Γ ⊢ x₁ ~ x₂ |> Y` and `Ty₊ X` conclude `Γ ⊢ x₁ ≅ x₂ <| X`.
  --       let ⟨Y, prf⟩ <- TmE.inferM Γ x₁' x₂' -- and Y must necessarily be convertible to X'
  --       -- let d : Q(TyWConv $Γ $X' $Y) := q(sorry)
  --       -- throwError "TmE.isDefEqM: pos-neu not yet implemented"
  --       return q(TmEDefEq.red_cert $X_red $x₁_red $x₂_red <| TmEDefEq.neu_inf (B := $Y) (A := $X') $prf)
  --     | _, _ => throwError "TmE.isDefEqM: type-case .U: Don't know how to match x₁'={x₁'}, x₂'={x₂'}"
  --   | _ => throwError "TmE.isDefEqM: Don't know how to match X'={X'}"

  /-- `Γ ⊢ x ≅ₕ y <| T` Reduced terms are convertible at type T. -/
  partial def TmQ.isDefEqRed (T : TyQ Γ) (x y : TmQ Γ T) : MetaM (TmHConvQ x y) := do
    have Γq : Q(Con) := Γ.quote
    have Tq : Q(Ty $Γq) := T.stripConv -- stripConv is dangerous
    have xq : Q(Tm $Γq $Tq) := x.stripConv -- stripConv is dangerous
    have yq : Q(Tm $Γq $Tq) := y.stripConv -- stripConv is dangerous
    match Tq with
    -- | ~q(Ty.Pi $A $B) => -- __negative__: Want `Γ ⊢ x₁ ≅ₕ x₂ : Pi A B`, so do η-expansion
    --   sorry
    | ~q(Ty.U) => -- __NeuPos__
      let S : Q(Ty $Γq) <- mkFreshExprMVarQ q(Ty $Γq)
      let x_conv_y : TmConvQ x y <- @TmQ.infer Γ S x y
      return x_conv_y
    | _ => throwError "{Expr.const `TmQ.isDefEqRed []}: Don't know how to handle\n  {xq}\n≅ₕ\n  {yq}\n<|\n  {Tq}"
    -- match xq, yq with
    -- | _, _ => throwError "{Expr.const `TmQ.isDefEqRed []}: Don't know how to handle\n  {xq}\n≅ₕ\n  {yq}\n<|\n  {Tq}"

  /-- `Γ ⊢ X ≅ₕ Y <|` Reduced types are convertible. -/
  partial def TyQ.isDefEqRed (X Y : TyQ Γ) : MetaM (TyConvQ X Y) := do
    have Γq : Q(Con) := Γ.quote
    have Xq : Q(Ty $Γq) := X.stripConv -- stripConv is dangerous
    have Yq : Q(Ty $Γq) := Y.stripConv -- stripConv is dangerous
    match Xq, Yq with -- What if we encounter a `.conv`? We can ignore it in this case, because this algorithm never looks at the context (the context is (almost) only there for documentation purposes).
    | ~q(Ty.U), ~q(Ty.U) => return TyConvQ.refl X
    | ~q(.Pi $A₁ $B₁), ~q(.Pi $A₂ $B₂) =>
      let dA <- @TyQ.isDefEq Γ A₁ A₂
      let c : ConConvQ (.ext Γ `anonymous A₂) (.ext Γ `anonymous A₁) := ConConvQ.ext' (.symm dA)
      let B₂  : TyQ (.ext Γ `anonymous A₂) := B₂
      let B₂' : TyQ (.ext Γ `anonymous A₁) := TyQ.conv c B₂ -- ? For this algorithm, we don't need .conv actually, right?
      let dB <- @TyQ.isDefEq (ConQ.ext Γ `anonymous A₁) B₁ B₂'
      let e /- : `Γ ⊢ .Pi A₁ B₁ ≅ .Pi A₂ (B₂.conv _)` -/ := mkAppN q(@TyConv.Pi) #[Γq, A₁, A₂, B₁, B₂', dA, dB]
      return e
    | ~q(.El $t₁), ~q(.El $t₂) =>
      let dt <- @TmQ.isDefEq Γ TyQ.U t₁ t₂
      return mkAppN q(@TyConv.El) #[Γ.quote, t₁, t₂, dt]
    | _ => throwError m!"{Expr.const `TyQ.isDefEqRed []}: Don't know how to handle {Xq} ≅ₕ {Yq}"
    -- | _ => throwError "TyQ.isDefEqRed: Don't know how to handle {Xq} ≅ₕ {Yq}"

  /-- `Γ ⊢ x ≅ y <| T` Terms are convertible at type T. -/
  partial def TmQ.isDefEq (T : TyQ Γ) (x y : TmQ Γ T) : MetaM (TmHConvQ x y) := do
    let ⟨X, xr, x_red_xr⟩ <- TmQ.red x
    let ⟨Y, yr, y_red_yr⟩ <- TmQ.red y
    let xr_conv_yr <- TmQ.isDefEqRed T xr yr
    return .trans (.trans x_red_xr xr_conv_yr) (.symm y_red_yr)

  /-- `Γ ⊢ X ≅ Y <|` Types are convertible. -/
  partial def TyQ.isDefEq (X Y : TyQ Γ) : MetaM (TyConvQ X Y) := do
    -- ? Here, we want to reduce away substitutions, but not necessarily conversion stuff.
    let ⟨Xr, X_red_Xr⟩ <- TyQ.red X
    let ⟨Yr, Y_red_Yr⟩ <- TyQ.red Y
    let Xr_conv_Yr <- TyQ.isDefEqRed Xr Yr
    return TyConvQ.trans (TyConvQ.trans X_red_Xr Xr_conv_Yr) (TyConvQ.symm Y_red_Yr)
end

/-
  # Elaborator
-/

mutual
  partial def elabTy (Γ : ConQ) (stx : Term) : TermElabM (TyQ Γ) := withRef stx do
    -- withTraceNode `stx.elab (niceLog m!"elabTy: {stx}") do
    match stx with
    | `(Sum $A $B) =>
      let A <- elabTy Γ A
      let B <- elabTy Γ B
      let e := TyQ.Sum A B
      addTermInfo' stx e
      return e
    | `(term| Unit) =>
      let e := TyQ.Unit
      addTermInfo' stx e
      return e
    | `(Type) =>
      let e := TyQ.U
      addTermInfo' stx e
      return e
    | `($stx_A -> $stx_B) =>
      let A : TyQ Γ <- elabTy Γ stx_A
      let B : TyQ (.ext Γ `anonymous A) <- elabTy (.ext Γ `anonymous A) stx_B
      let e := TyQ.Pi `anonymous A B
      addTermInfo' stx e
      return e
    | `(($stx_a:ident : $stx_A) -> $stx_B) =>
      let A : TyQ Γ <- elabTy Γ stx_A
      let name := stx_a.getId
      withLocalDeclD stx_a.getId A fun a_fv => do -- add a LocalDecl `a : A`, where `A` is not actually a Lean `Type`, but... it's just for visualization.
        addTermInfo' (isBinder := true) stx_a a_fv
        let B : TyQ (.ext Γ name A) <- elabTy (.ext Γ name A) stx_B
        let e := TyQ.Pi name A B
        addTermInfo' stx e
        return e
    | _ => -- if none of the type things match, try to elab as a Tm.
      let T <- elabTm Γ TyQ.U stx
      return .El T

  /-- Elaborates term, inferring *reduced* type. `Γ ⊢ stx |>ₕ X` -/
  partial def elabTmInferring (Γ : ConQ) (stx : Term) : TermElabM <| (X : TyQ Γ) × (TmQ Γ X) := withRef stx do
    let ⟨X, t⟩ <- elabTmInferring' Γ stx
    let ⟨Xr, X_red_Xr⟩ <- TyQ.red X
    if <- Meta.isDefEq X Xr then return ⟨Xr, t⟩ -- optimization to avoid needless `.conv`
    -- have `t : X`, but need `Tm.conv t _ : Xr`
    let t' : TmQ Γ Xr := TmQ.conv X_red_Xr t
    addTermInfo' stx t'
    return ⟨Xr, t'⟩

  /-- Elaborates term, inferring type. `Γ ⊢ stx |> out_X` -/
  partial def elabTmInferring' (Γ : ConQ) (stx : Term) : TermElabM <| (X : TyQ Γ) × (TmQ Γ X) := withRef stx do
    -- withTraceNode `stx.elab (niceLog m! "elabTmInferring': {stx}") do
    match stx with
    | `($id:ident) =>
      have Γq : Q(Con) := Γ.quote
      let .some v := Γ.findVar id.getId | throwError "elabTmInferring': No such variable"
      let .some ⟨X, v⟩ := @VarQ.quote Γ v | throwError "elabTmInferring': Could not quote variable"
      have X : Q(Ty $Γq) := X
      let v : Q(Var $Γq $X) := v
      let t : Q(Tm $Γq $X) := q(@Tm.var $Γq $X $v)
      return ⟨X, t⟩
    | `($stx_f $stx_a) =>
      have Γq := Γ.quote
      let ⟨F, f⟩ <- elabTmInferring Γ stx_f -- `Γ ⊢ f |>ₕ Pi A B`
      have F : Q(Ty $Γq) := F
      have f : Q(Tm $Γq $F) := f
      let A : Q(Ty $Γq) <- mkFreshExprMVarQ q(Ty $Γq)
      let B : Q(Ty (.ext $Γq $A)) <- mkFreshExprMVarQ q(Ty (.ext $Γq $A))
      let ⟨_prf⟩ <- assertDefEqQ q($F) q(@Ty.Pi $Γq $A $B) -- assign A and B. We can assume that `F` is some `.Pi _ _`, because elabTmInferring also reduces the type for us, computing away substitutions and some other stuff.
      let a : TmQ Γ A <- elabTm Γ A stx_a -- `Γ ⊢ a <| A`
      let Ba : TyQ Γ := TyQ.subst B (SubstQ.apply a) -- `B[Subst.cons .id (Tm.conv a _)]`
      return ⟨Ba, TmQ.app (name := `anonymous) f a⟩ -- `Γ ⊢ f a |> B[⟨id, a.conv _⟩]`
    | `(fun ($stx_a:ident : $stx_A) => $stx_body)
    | `(fun  $stx_a:ident : $stx_A  => $stx_body) =>
      let name := stx_a.getId
      let A : TyQ Γ <- elabTy Γ stx_A -- `Γ ⊢ A <|`
      withLocalDeclD name A fun a_fv => do
        addTermInfo' (isBinder := true) stx_a a_fv
        let ⟨B, body⟩ <- elabTmInferring (.ext Γ name A) stx_body -- `Γ; A ⊢ body |> B`
        let X : TyQ Γ := TyQ.Pi name A B
        let lam : TmQ Γ X := TmQ.lam body
        addTermInfo' stx lam
        return ⟨X, lam⟩ -- therefore `Γ ⊢ fun (a : A) => body |> Pi A B`
    | `(( $stx_t:term )) => elabTmInferring Γ stx_t
    | _ => throwUnsupportedSyntax

  partial def elabTm (Γ : ConQ) (A : TyQ Γ) (stx : Term) : TermElabM (TmQ Γ A) := withRef stx do
    let ⟨A', t⟩ <- elabTmInferring Γ stx
    if <- Meta.isDefEq A' A then -- This `Meta.isDefEq` is only an optimization to avoid needless `Tm.conv`
      return t
    else
      let c : @TyConvQ Γ A' A <- TyQ.isDefEq A' A
      return TmQ.conv c t
end

elab "Tm(" t:term ")" : term <= Expected => do
  let Γ : ConQ := .nil
  let X : Q(Ty .nil) <- mkFreshExprMVarQ q(Ty .nil)
  if <- isDefEq q(Tm .nil $X) Expected then
      elabTm Γ X t
  else
    throwError "Oh no"

elab "Ty(" T:term ")" : term => do
  let Γ : ConQ := .nil
  elabTy Γ T

open Notation
open Ty Tm Var Subst
set_option pp.fieldNotation.generalized false

#check Ty(Type)
#check Ty(Type -> Type)
#check Ty((A : Type) -> A)
#check Ty((A : Type) -> (a : A) -> A)
#check Ty((A : Type) -> (B : Type) -> (a : A) -> A)

#check (Ty( (A : Type -> Type) -> (B : Type) -> A B ) : Ty .nil)

#check (Ty((A : Type) -> Sum A A) : Ty .nil)
#check (Ty( (A : Type -> Type) -> (B : Type) -> (A B) -> B) : Ty .nil)
#check (Ty( (A : Type -> Type) -> (B : Type) -> A B -> B) : Ty .nil)
#check (Ty( (A : Type) -> Sum A Unit -> A -> Type ) : Ty .nil)
#check (Ty( (A : Type) -> Sum Unit A -> A -> Type ) : Ty .nil)
#check (Ty( (A : Type) -> (B : A -> Type) -> (a : A) -> B a ) : Ty .nil)
#check (Ty( (A : Type) -> (B : A -> Type) -> (a : A) -> B a -> B a) : Ty .nil)
#check (Ty( (A : Type) -> (B : A -> Type) -> (a : A) -> (ba : B a) -> Sum (B a) A ) : Ty .nil)

def ex := Ty( (A : Type) -> A)
set_option pp.all true in
#print ex

#check Tm(fun (x : Unit) => x)

private def _ff : Tm .nil Ty((A : Type) -> Sum Unit Unit -> Type) :=
  Tm( fun (A : Type) => fun (sum : Sum Unit Unit) => A)

open Con Ty Tm Var Subst

def test1 : Ty .nil := Ty((a : Type) -> (b : Type) -> a)
#print test1

def test2 : Ty .nil := Ty((A : Type -> Type) -> (B : Type) -> B -> A B)
#print test2

def my_id : Tm .nil Ty((A : Type) -> A -> A)
  := Tm(fun A : Type => fun x : A => x)

-- P : U -> U, x: U, z : P x |- z : P (id x)
def test6 : Ty .nil := Ty(
  (P : Type -> Type) ->
  (X : Type) ->
  (z : P ((fun x:Type => x) X) ) ->
  (F : P X -> Type) ->
  F z
)
