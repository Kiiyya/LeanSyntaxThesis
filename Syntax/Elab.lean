import Aesop
import Qq
import Lean
import Syntax.Erased
import Syntax.Wellformed
import Syntax.AllTogether
import Syntax.Trace

set_option linter.unusedVariables false

/-
  Elaborator.
  Converts `Lean.Syntax` into `Q(Tm _ _)`.

  Largely based on "What does it take to certify a conversion checker?" by Meven Lennon-Bertrand.
  See the paper at https://arxiv.org/pdf/2502.15500, especially the appendix B.
-/

open Lean Meta Elab Term Qq


def myLog [Monad m] [MonadLiftT MetaM m] [MonadExcept Exception m] (f_ok : α -> m MessageData) (f_err : Exception -> m MessageData := fun e => throw e) : Except Exception α → m MessageData
| .ok val => f_ok val
| .error e => f_err e

def niceLog [Monad m] [MonadLiftT MetaM m] [MonadExcept Exception m] [ToMessageData α]
  (wher : MessageData)
  (f_ok : α -> m MessageData := fun a => return toMessageData a)
  : Except Exception α → m MessageData
  := myLog
      (fun res => return m!"{wher} ==> {toMessageData res}")
      (fun err => return m!"{wher} ==> ERROR {err.toMessageData}")

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
def SubstQ (Γ Δ : ConQ) : Type := Expr
def ConConvQ (Γ Δ : ConQ) : Type := Expr
def TyConvQ {Γ : ConQ} (X Y : TyQ Γ) : Type := Expr
def TmConvQ {Γ : ConQ} {A : TyQ Γ} (x y : TmQ Γ A) : Type := Expr

instance : Inhabited ConQ := ⟨.nil⟩
instance : Inhabited (TmQ Γ A) := ⟨Expr.bvar 0⟩

@[match_pattern] def ConQ.ext : (Γ : ConQ) -> Name -> TyQ Γ -> ConQ := fun Γ name A => ConQ.ext' Γ name A

def TyQ.unsafeIntro : Expr -> TyQ Γ := id
def TmQ.unsafeIntro : Expr -> TmQ Γ A := id
def SubstQ.unsafeIntro : Expr -> SubstQ Γ Δ := id
def ConConvQ.unsafeIntro : Expr -> ConConvQ Γ Δ := id
def TyConvQ.unsafeIntro : Expr -> TyConvQ X Y := id
def TmConvQ.unsafeIntro : Expr -> TmConvQ x y := id

def TyQ.unsafeCast : TyQ Γ -> TyQ Γ' := id
def TmQ.unsafeCast : TmQ Γ A -> TmQ Γ' A' := id
def SubstQ.unsafeCast : SubstQ Γ Δ -> SubstQ Γ' Δ' := id
def ConConvQ.unsafeCast : ConConvQ Γ Δ -> ConConvQ Γ' Δ' := id
def TyConvQ.unsafeCast : TyConvQ X Y -> TyConvQ X' Y' := id
def TmConvQ.unsafeCast : TmConvQ x y -> TmConvQ x' y' := id
def TmConvQ.unsafeCast! {x : TmQ Γ X} {y : TmQ Γ Y} : @TmConvQ Γ X x y -> TmConvQ x' y' := id

partial def ConQ.fromExpr (e : Q(Con)) : ConQ :=
  match_expr e with
  | Con.nil => .nil
  | Con.ext Γ A => ConQ.ext (fromExpr Γ) `anonymous (.unsafeIntro A)
  | _ => .unknown e

def ConQ.quote : ConQ -> Q(Con)
| .nil => q(Con.nil)
| .ext Γq name Aq =>
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

def SubstQ.wk (σ : SubstQ Γ Δ) : SubstQ (Γ.ext name W) Δ :=
  have Γq : Q(Con) := Γ.quote
  have Δq : Q(Con) := Δ.quote
  have W : Q(Ty $Γq) := W.quote
  have σ : Q(Subst $Γq $Δq) := σ.quote
  q(@Subst.wk $Γq $Δq $W $σ)

def TmQ.app (f : TmQ Γ (.Pi name A B)) (a : TmQ Γ A) : TmQ Γ (TyQ.subst B (.apply a))
  := mkAppN q(@Tm.app) #[ Γ.quote, A.quote, B.quote, f.quote, a.quote ]

def TmQ.lam {Γ name} {A : TyQ Γ} {B : TyQ (.ext Γ name A)} (body : TmQ (.ext Γ name A) B) : TmQ Γ (TyQ.Pi name A B)
  := mkAppN q(@Tm.lam) #[ Γ.quote, A.quote, B.quote, body.quote ]

def TyQ.conv {Γ Δ : ConQ} (c : ConConvQ Γ Δ) (A : TyQ Γ) : TyQ Δ :=
  mkAppN q(@Ty.conv) #[Γ.quote, Δ.quote, c.quote, A.quote]

def TmQ.conv {Γ : ConQ} {X Y : TyQ Γ} (c : TyConvQ X Y) (t : TmQ Γ X) : TmQ Γ Y :=
  mkAppN q(@Tm.conv) #[Γ.quote, X.quote, Y.quote, c.quote, t.quote]

def SubstQ.wki {Γ : ConQ} {W : TyQ Γ} : SubstQ (.ext Γ name W) Γ := mkAppN q(@Subst.wki) #[Γ, W]

inductive VarQ : (Γ : ConQ) -> TyQ Γ -> Type where
| vz : VarQ (.ext Γ name A) (TyQ.subst A .wki)
| vs : VarQ Γ A -> VarQ (.ext Γ name B) (A.subst .wki)
| unsafeCast : VarQ Γ A -> VarQ Δ B

def ConQ.findVar! (n : Name) : (Γ : ConQ) -> Option <| (T : TyQ Γ) × (VarQ Γ T)
| .nil => none
| .ext Γ name B =>
  if n = name then
    some ⟨B.subst .wki, .vz⟩
  else
    (Γ.findVar! n).map fun ⟨X, v⟩ => ⟨X.subst .wki, .vs v⟩
| .unknown expr => none

def VarQ.quote : {Γ : ConQ} -> {A : TyQ Γ} -> (v : VarQ Γ A) -> Expr
| .ext Γ name A, _, .vz   => -- expected `Var (Γ; A) A[wki]`
  have Γq : Q(Con) := Γ.quote
  have Aq : Q(Ty $Γq) := A
  let Xq : Q(Ty (.ext $Γq $Aq)) := q(Ty.subst $Aq .wki)
  have vq : Q(Var (.ext $Γq $Aq) $Xq) := q(.vz)
  vq
| .ext Γ name B, _, VarQ.vs (A := A) v => Id.run do -- expected `Var (Γ; B) A[wki]`
  have Γq : Q(Con) := Γ.quote
  have Aq : Q(Ty $Γq) := A
  have Bq : Q(Ty $Γq) := B
  let ih : Q(Var $Γq $Aq) := v.quote
  let ret : Q(Var (.ext $Γq $Bq) (.subst $Aq .wki)) := q(.vs $ih)
  ret
| Γ, _, .unsafeCast v => v.quote

def TmQ.var (v : VarQ Γ T) : TmQ Γ T := mkAppN q(@Tm.var) #[Γ, T, v.quote]

partial def VarQ.fromExprUnsafe (e : Expr) : MetaM <| VarQ Γ T := do
  match_expr e with
  | Var.vz _ _ =>
    match Γ with
    | .nil => throwError "a"
    | .ext Γ name A =>
      let ret := @VarQ.vz Γ name A
      return .unsafeCast ret
    | .unknown _ => throwError "a"
  | Var.vs ___Γ A _B v =>
    match h : Γ with
    | .nil => throwError "a"
    | .ext Γ name B =>
      let A : TyQ Γ := A
      -- v : `Var Γ A`
      let ih : VarQ Γ A <- VarQ.fromExprUnsafe v
      let ret : VarQ (.ext Γ name B) (.subst A .wki) := .vs ih
      return .unsafeCast ret
    | .unknown Δ => throwError "VarQ.fromExprUnsafe: Ran out of context. Below is {Δ}"
  | _ => throwError "VarQ.fromExprUnsafe: Don't know how to handle {e}"

def VarQ.toNat : VarQ Γ A -> Nat
| .vz => 0
| .vs v => v.toNat + 1
| .unsafeCast v => v.toNat

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
  (Bc : @TyConvQ (.ext Γ `anonymous A) B (B'.conv (.ext' Ac.symm)))
  -- (Bc : @TyConvQ (.ext Γ `anonymous A) B B')
  -- (Bc : Expr)
  : TyConvQ (.Pi `anonymous A B) (.Pi `anonymous A' B')
  := sorry

def TyConvQ.El (t1 t2 : TmQ Γ .U) (c : TmConvQ t1 t2) : TyConvQ (.El t1) (.El t2) :=
  mkAppN q(@TyConv.El) #[Γ, t1, t2, c]

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

def TmQ.subst {A : TyQ Δ} (t : TmQ Δ A) (σ : SubstQ Γ Δ) : TmQ Γ (A.subst σ)
  := .unsafeIntro <| mkAppN q(@Tm.subst) #[Γ.quote, Δ.quote, A, t, σ]

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

def TmHConvQ.refl (x : TmQ Γ X) : TmHConvQ x x where
  tyConv := .refl X
  tmConv := TmConvQ.refl x

def TmHConvQ.symm (xy : @TmHConvQ Γ X Y x y) : TmHConvQ y x :=
  let tyConv := xy.tyConv.symm
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

def TyConvQ.bySorry {X Y : TyQ Γ} : TyConvQ X Y :=
  have Γq : Q(Con) := Γ.quote
  have X : Q(Ty $Γq) := X
  have Y : Q(Ty $Γq) := Y
  let sry : Q(@TyConv $Γq $X $Y) := q(sorry)
  sry

def TmConvQ.bySorry {x y : TmQ Γ T} : TmConvQ x y :=
  have Γq : Q(Con) := Γ.quote
  have Tq : Q(Ty $Γq) := T.quote
  have x : Q(Tm $Γq $Tq) := x
  have y : Q(Tm $Γq $Tq) := y
  let sry : Q(@TmConv $Γq $Tq $x $y) := q(sorry)
  sry
def TmHConvQ.bySorry {x : TmQ Γ X} {y : TmQ Γ Y} : TmHConvQ x y :=
  have Γq : Q(Con) := Γ.quote
  have Xq : Q(Ty $Γq) := X.quote
  have Yq : Q(Ty $Γq) := Y.quote
  have x : Q(Tm $Γq $Xq) := x
  have y : Q(Tm $Γq $Yq) := y
  let sry : Q(@TmHConv $Γq $Xq $Yq $x $y) := q(sorry)
  TmHConvQ.ofExpr sry

attribute [irreducible] TyQ
attribute [irreducible] TmQ
attribute [irreducible] SubstQ
attribute [irreducible] ConConvQ
attribute [irreducible] TyConvQ
attribute [irreducible] TmConvQ

/-
  ## Matchers
-/

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

partial def TmQ.isApp {Γ : ConQ} {T : TyQ Γ} (t : TmQ Γ T) : MetaM <| Option (IsAppResult t) := do
  match_expr t with
  | Tm.app _ A B f a =>
    let A : TyQ Γ := .unsafeIntro A
    let B : TyQ (.ext Γ `anonymous A) := .unsafeIntro B
    let f : TmQ Γ (.Pi `anonymous A B) := .unsafeIntro f
    let a : TmQ Γ A := .unsafeIntro a
    let T_conv_Ba : TyConvQ T (TyQ.subst B (SubstQ.apply a)) := (TyConvQ.refl T).unsafeCast -- okay because `T ≡ B[a]` is defeq
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
    return some { name, A, B, f, a, conv }
  -- | Tm.subst .. => or maybe just handle this elsewhere
  | _ => return none

structure IsVarResult (t : TmQ Γ T) where
  X : TyQ Γ
  var : VarQ Γ X
  conv : TmHConvQ t (.var var)

partial def TmQ.isVar {Γ : ConQ} {T : TyQ Γ} (t : TmQ Γ T) : MetaM <| Option (IsVarResult t) := do
  match_expr t with
  | Tm.var _ A v =>
    let A : TyQ Γ := .unsafeIntro A
    let v <- VarQ.fromExprUnsafe v
    return some ⟨A, v, .unsafeCast (.refl (.var v))⟩ -- okay because defeq
  | Tm.conv _ X _T X_conv_T t' =>
    let X : TyQ Γ := .unsafeIntro X
    let t' : TmQ Γ X := .unsafeIntro t'
    let some ⟨Z, var, conv⟩ <- t'.isVar | return none
    return some ⟨Z, var, .bySorry⟩
  | _ => return none

structure IsLamResult (t : TmQ Γ T) where
  name : Name := `anonymous
  A : TyQ Γ
  B : TyQ (.ext Γ name A)
  body : TmQ (.ext Γ name A) B
  conv : TmHConvQ t (.lam body)

partial def TmQ.isLam {Γ : ConQ} {T : TyQ Γ} (t : TmQ Γ T) : MetaM <| Option (IsLamResult t) := do
  match_expr t with
  | Tm.lam _ A B body =>
    let A : TyQ Γ := .unsafeIntro A
    let B : TyQ (.ext Γ `anonymous A) := .unsafeIntro B
    let body : TmQ (.ext Γ `anonymous A) B := .unsafeIntro body
    let Conv : TyConvQ T (TyQ.Pi `anonymous A B) := .unsafeCast (.refl T) -- okay because this is a defeq
    let conv := .unsafeCast (.refl t) -- okay because defeq
    return some { A, B, body, conv }
  | Tm.conv _ X __T X_conv_T t' =>
    have X : TyQ Γ := .unsafeIntro X
    have t' : TmQ Γ X := .unsafeIntro t'
    have X_conv_T : TyConvQ X T := .unsafeIntro X_conv_T
    let some {name, A, B, body, conv } <- TmQ.isLam t' | return none
    let T_conv_PiAB : TyConvQ T (.Pi name A B) := .trans X_conv_T.symm conv.tyConv
    let conv := .bySorry
    return some { name, A, B, body, conv }
  | _ => return none

structure IsSubstTyResult (Y : TyQ Γ) where
  Δ : ConQ
  X : TyQ Δ
  σ : SubstQ Γ Δ
  conv : TyConvQ Y (X.subst σ)

partial def TyQ.isSubst {Γ : ConQ} {Y : TyQ Γ} : MetaM <| Option (IsSubstTyResult Y) :=
  withTraceNode `stx.isQ (myLog (f_err := fun err => return m!"TyQ.isSubst\n  {Y.quote}\n~~> ERROR {err.toMessageData}") (fun res => return m!"TyQ.isSubst {Y.quote} is some? {res.isSome}")) do
  match_expr Y with
  | Ty.subst _ Δ X σ =>
    let Δ : ConQ := .fromExpr Δ
    let X : TyQ Δ := .unsafeIntro X
    let σ : SubstQ Γ Δ := .unsafeIntro σ
    return some { Δ, X, σ, conv := (TyConvQ.refl Y).unsafeCast } -- okay because defeq
  | Ty.conv _ _ _ _ => throwError "TyQ.isSubst: not yet impl for Ty.conv"
  -- todo look through conv
  | _ => return none

structure IsSubstTmResult (y : TmQ Γ Aσ) where
  Δ : ConQ
  A : TyQ Δ
  x : TmQ Δ A
  σ : SubstQ Γ Δ
  conv : TmHConvQ y (TmQ.subst x σ)

partial def TmQ.isSubst {Γ : ConQ} {Aσ : TyQ Γ} (y : TmQ Γ Aσ) : MetaM <| Option (IsSubstTmResult y) :=
  withTraceNode `stx.isQ (myLog (f_err := fun err => return m!"TmQ.isSubst\n  {y.quote}\n~~> ERROR {err.toMessageData}") (fun res => return m!"TmQ.isSubst {y.quote} is some? {res.isSome}")) do
  match_expr y with
  | Tm.subst _ Δ A x σ =>
    let Δ : ConQ := .fromExpr Δ
    let A : TyQ Δ := .unsafeIntro A
    let x : TmQ Δ A := .unsafeIntro x
    let σ : SubstQ Γ Δ := .unsafeIntro σ
    return some { Δ, A, σ, x, conv := (TmHConvQ.refl y).unsafeCast }
  | Tm.conv _ A _B c t =>
    let A : TyQ Γ := .unsafeIntro A
    let c : TyConvQ A Aσ := .unsafeIntro c
    let t : TmQ Γ A := .unsafeIntro t
    let some ⟨Δ, C, z, δ, conv⟩ <- TmQ.isSubst t | return none
    return some ⟨Δ, C, z, δ, .bySorry⟩
  | _ => return none

def ConQ.isExt : ConQ -> (MetaM <| (Γ : ConQ) × Name × TyQ Γ)
| .nil => throwError "ConQ.isExt: Actually, is nil."
| .ext' Γ name A => return ⟨Γ, name, .unsafeIntro A⟩
| .unknown Γ => throwError "ConQ.isExt: Actually is unknown {Γ}. Not yet implemented."

/-
  # Reduction
  It might be helpful to have a dedicated reduction relation, instead of piggybacking on TyConv.

  We also reduce away substitutions as far as possible.
-/

partial def VarQ.subst {Γ Δ : ConQ} {A} (v : VarQ Δ A) (σ : SubstQ Γ Δ) : MetaM <| TmQ Γ (A.subst σ) := do
  match_expr σ with
  | Subst.id _ =>
    -- we have `Γ ≡ Δ`
    let ret : TmQ Δ A := TmQ.var v
    let A : TyQ Γ := .unsafeCast A
    let ret : TmQ Γ A := .unsafeCast ret
    return ret.conv .bySorry
  | Subst.wki _Δ W => -- `v[wki] = (vs v)`
    -- have `Γ ≡ Δ;W`
    let W : TyQ Δ := .unsafeIntro W
    let σ : SubstQ (.ext Δ `anonymous W) Δ := σ.unsafeCast
    let A : TyQ Δ := A.unsafeCast
    let v : VarQ Δ A := v.unsafeCast
    let ret : TmQ (.ext Δ `anonymous W) (.subst A .wki) := .var (.vs v) -- `v[wki] = vs v`
    return ret.unsafeCast
  | Subst.lift Γ' Δ' W' σ' => -- `(vs v)[lift σ'] = v[wk σ']`
    -- `Γ ≡ Γ';W'[σ']` and `Δ ≡ Δ';W'`
    let ⟨Γ', name, Wσ⟩ <- Γ.isExt
    let ⟨Δ', _, W'⟩ <- Δ.isExt
    let σ' : SubstQ Γ' Δ' := .unsafeIntro σ'
    match h : v with
    | .vz =>
      -- `A ≡ A'[wki]` and `A' ≡ W'`, thus `A ≡ W'[wki]`, thus `W'[]`
      let ret : TmQ (.ext Γ' name (W'.subst σ')) ((W'.subst σ').subst .wki) := .var .vz -- `Γ' ⊢ vz : W'[σ'][wki]`
      let c : TyConvQ ((W'.subst σ').subst .wki) ((W'.subst .wki).subst σ'.lift) := .bySorry
      let ret : TmQ (.ext Γ' name (W'.subst σ')) ((W'.subst .wki).subst σ'.lift) := ret.conv c -- `Γ' ⊢ vz : W'[lift σ'][wki]`
      return ret.unsafeCast
    | .vs (Γ := Δ'') (name := name'') (A := A'') (B := B'') v =>
      -- let v : VarQ Δ' A' := v -- we can't use unsafeCast here because that'd result in an endless loop...
      -- `A ≡ A'[wki]` and `B' ≡ W'`
      let σ'' : SubstQ Γ' Δ'' := .unsafeIntro σ'
      let ret : TmQ (.ext Γ' name (B''.subst σ'')) _ <- VarQ.subst v (.wk σ'')
      let ret : TmQ (.ext Γ' name (B''.subst σ'')) ((A''.subst .wki).subst σ''.lift) := ret.conv .bySorry
      return ret.unsafeCast
    | @VarQ.unsafeCast _Δ _A _ _ v =>
      -- retry. this actually ignores that we already matched lift, but that's fine.
      let ih <- @VarQ.subst Γ _Δ _A v σ.unsafeCast
      return ih.unsafeCast
  | Subst.comp _Γ Θ _Δ σ1 σ2 =>
    let Θ : ConQ := .fromExpr Θ
    let σ1 : SubstQ Θ Δ := .unsafeIntro σ1
    let σ2 : SubstQ Γ Θ := .unsafeIntro σ2
    let ih1 <- VarQ.subst v σ1
    let ret : TmQ Γ (A |>.subst σ1 |>.subst σ2) := ih1.subst σ2
    let ret : TmQ Γ (A.subst (.comp σ1 σ2)) := ret.conv .bySorry
    return ret.unsafeCast
  | Subst.apply _Γ _ a =>
    match h : v with
    | .vz =>
      let ⟨Γ', _, A'⟩ <- Δ.isExt
      let a : TmQ Γ' A' := .unsafeIntro a
      -- have c : TyConvQ A' (A'.subst (.wki (W := A')) |>.subst (.apply a)) := sorry
      -- let ret : TmQ Γ' (A'.subst .wki |>.subst (.apply a)) := a.conv c
      return a.unsafeCast -- not 100% sure this is okay. But, `A'[wki][apply _]` should be defeq to A' always right?
    | .vs v => throwError "VarQ.subst: apply with vs not yet impl: {v.toNat}[{σ.quote}]"
    | @VarQ.unsafeCast _Δ _A _ _ v =>
      let ih <- @VarQ.subst Γ _Δ _A v σ.unsafeCast
      return ih.unsafeCast
  | _ =>
    throwError "VarQ.subst: Don't know how to handle {v.toNat}[{σ.quote}]"

mutual
  -- Ignore the extra return type `Y` if it confuses you. Reduction works on preterms in the paper anyway.
  partial def TmQ.red {Γ : ConQ} {X : TyQ Γ} (x : TmQ Γ X) : MetaM <| (Y : TyQ Γ) × (y : TmQ Γ Y) × TmHConvQ x y := do
    withTraceNode `stx.red (myLog (f_err := fun err => return m!"TmQ.red\n  {x.quote}\n~~> ERROR {err.toMessageData}") (fun ⟨Y, y, prf⟩ => return m!"TmQ.red\n  {x.quote}\n~~>\n  {y.quote}\nProof: {prf.quote}")) do
    let cont {Y} (y : TmQ Γ Y) (x_red_y : TmHConvQ x y) : MetaM <| (Z : TyQ Γ) × (z : TmQ Γ Z) × TmHConvQ x z := do
      let ⟨Z, z, y_red_z⟩ <- TmQ.red y
      let x_red_z := TmHConvQ.trans (Γ := Γ) (x := x) x_red_y y_red_z
      return ⟨Z, z, x_red_z⟩

    if let some ⟨Θ, X', x', σ1, conv⟩ <- x.isSubst then
      if let some ⟨Δ, X'', x'', σ2, conv₂⟩ <- x'.isSubst then
        -- `x''[σ2][σ1] = x''[σ2 ∘ σ1]`
        let σ := SubstQ.comp σ2 σ1
        let Y := TyQ.subst X'' σ
        let y := TmQ.subst x'' σ
        have Prf : @TyConvQ Γ ((X''.subst σ2).subst σ1) Y := .subst_comp
        have prf : TmHConvQ ((x''.subst σ2).subst σ1) y := .bySorry
        have tmp := conv₂.subst σ1
        have tmp := conv.trans tmp
        return <- cont y (tmp.trans prf)

    if let .some ⟨Δ, C, t, σ, x_conv_tσ⟩ <- x.isSubst then
      -- `x ≡ t[σ] : C[σ]` with `T ≡ C[σ]`
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
      if let .some ⟨name, A, B, body, conv⟩ <- t.isLam then
        let Aσ := TyQ.subst A σ
        let Bσ := TyQ.subst B σ.lift
        let bodyσ : TmQ (.ext Γ name Aσ) Bσ := TmQ.subst body σ.lift
        let Y : TyQ Γ := .Pi name Aσ Bσ
        let y : TmQ Γ Y := .lam bodyσ
        return <- cont y .bySorry
      if let .some ⟨V, v, conv_v⟩ <- t.isVar then
        let y : TmQ Γ (V.subst σ) <- VarQ.subst v σ
        return <- cont y .bySorry

    if let .some ⟨name, A, B, f, a, t_conv_app⟩ <- x.isApp then
      let ⟨Fr, fr, f_red_fr⟩ <- TmQ.red f -- We need to reduce f only because it might be a substitution. -- todo use f_red_fr
      if let .some ⟨name', A', B', body, f_conv_lam⟩ <- fr.isLam then
        let c : TyConvQ A A' := .bySorry
        let y : TmQ Γ (B'.subst (.apply (a.conv c))) := body.subst (.apply (a.conv c)) -- * beta reduction
        trace[stx.red] "Beta-reducing! New term: {y.quote}"
        return <- cont y .bySorry

    return ⟨X, x, .refl x⟩

  partial def TyQ.red {Γ : ConQ} (X : TyQ Γ) : MetaM <| (Y : TyQ Γ) × TyConvQ X Y := do
    withTraceNode `stx.red (myLog (f_err := fun err => return m!"TyQ.red\n  {X.quote}\n~~> ERROR {err.toMessageData}") (fun ⟨Y, prf⟩ => return m!"TyQ.red\n  {X.quote}\n~~>\n  {Y.quote}\nProof: {prf.quote}")) do
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
        trace[stx.red] "✓ isSubst..."
        -- logInfo m!"TyQ.red {X.quote}\n  but in subst already so X' is {X'.quote}"
        if let some ⟨conv2⟩ <- X'.isU then
          let Y := @TyQ.U Γ -- `U[σ] ≡ U`
          trace[stx.red] "  ✓ isU"
          return <- cont TyQ.U .bySorry -- actually don't need to cont here
        if let some ⟨name, A, B, conv⟩ <- X'.isPi then
          let Y := TyQ.Pi name (A.subst σ) (B.subst σ.lift) -- `(Pi A B)[σ] = Pi A[σ] B[lift σ]`
          trace[stx.red] "  ✓ isPi"
          return <- cont Y .bySorry -- actually dont need to cont here
        if let some ⟨t, conv⟩ <- X'.isEl then
          let y : TmQ Γ (.subst .U σ) := t.subst σ -- `(El t)[σ] = El t[σ]`
          let y : TmQ Γ .U := y.unsafeCast -- okay because this is a defeq -- ? not sure this is right
          trace[stx.red] "  ✓ isEl"
          return <- cont (.El y) .bySorry

      if let some ⟨t, conv⟩ <- X.isEl then -- pretend `El` is transparent (it's not a ctor in the conv-cert paper)
        let ⟨T, t', prf⟩ <- TmQ.red t
        let Y : TyQ Γ := .El t'.unsafeCast -- should be okay because `U.conv c ≡ U` right?
        return ⟨Y, .bySorry⟩
        -- return <- cont Y .bySorry

      -- logInfo m!"TyQ.red did not match anything for {X.quote}"
      return ⟨X, .refl X⟩
end

/-
  # Typed Algorithmic Conversion Checking
-/

structure TmQ.InferResult (x : TmQ Γ X) (y : TmQ Γ Y) where
  /-- The inferred type. -/
  T : TyQ Γ
  T_conv_X : TyConvQ T X
  T_conv_Y : TyConvQ T Y
  conv : TmHConvQ x y

structure TmQ.IsDefEqResult (x : TmQ Γ X) (y : TmQ Γ Y) (T : TyQ Γ) where
  T_conv_X : TyConvQ T X
  T_conv_Y : TyConvQ T Y
  conv : TmHConvQ x y

#check Ty.Pi.inj
def TyQ.Pi_inj (c : @TyConvQ Γ (.Pi a1 A₁ B₁) (.Pi a2 A₂ B₂))
  : (Ac : @TyConvQ Γ A₁ A₂) × @TyConvQ (.ext Γ a1 A₁) B₁ (B₂.conv (ConConvQ.ext' Ac.symm))
  := ⟨.bySorry, .bySorry⟩

set_option pp.fieldNotation.generalized false

mutual
  /-- `Γ ⊢ t ~ₕ t' |> T` Neutral terms are comparable, inferring the *reduced* type T. -/
  partial def TmQ.inferRed (x : TmQ Γ X) (y : TmQ Γ Y) : MetaM (TmQ.InferResult x y) := do
    let ⟨T, c1, c2, conv⟩ <- TmQ.infer x y
    let ⟨Tr, red⟩ <- TyQ.red T
    return ⟨Tr, .bySorry, .bySorry, .bySorry⟩

  /-- `Γ ⊢ x ~ y |> T` Neutral terms are comparable, inferring type T. -/
  partial def TmQ.infer_impl (x : TmQ Γ X) (y : TmQ Γ Y) : MetaM (TmQ.InferResult x y) := do
    if let some ⟨name1, A1, B1, n, u, Conv⟩ <- x.isApp then
      if let .some ⟨name2, A2, B2, n', u', Conv'⟩ <- y.isApp then
        -- __NApp__
        let ⟨T, T_conv_idk, T_conv_idk2, conv⟩ <- TmQ.inferRed n n'
        let some ⟨name, A, B, T_conv_PiAB⟩ <- T.isPi | throwError "TmQ.infer: NApp case, inferRed returned {T.quote} which is not a Pi"
        -- let A1c : TyConvQ A1 A := sorry
        -- let A2c : TyConvQ A2 A := sorry
        -- let B1c : TyConvQ B1 (B.conv (.ext' A1c.symm)) := sorry
        -- let B2c : TyConvQ B2 (B.conv (.ext' A2c.symm)) := sorry
        let ⟨conv1, conv2, conv⟩ <- TmQ.isDefEq u u' A
        let prf : TmHConvQ x y := .bySorry
        let prfX : TyConvQ (TyQ.Pi name A B) X := .bySorry
        let prfY : TyConvQ (TyQ.Pi name A B) Y := .bySorry
        return ⟨.Pi name A B, prfX, prfY, prf⟩
    if let some ⟨V1, v1, conv1⟩ <- x.isVar then
      if let some ⟨V2, v2, conv2⟩ <- y.isVar then
        if v1.toNat == v2.toNat then
          return ⟨X, .bySorry, .bySorry, .bySorry⟩
        else
          throwError "TmQ.infer: Variables do not match, lhs is {v1.toNat} while rhs is {v2.toNat}"
    throwError "{Expr.const `TmQ.infer []}: Don't know how to handle\n  {x.quote}\n~ {y.quote}\n"

  /-- `Γ ⊢ x ~ y |> T` Neutral terms are comparable, inferring type T. -/
  partial def TmQ.infer (x : TmQ Γ X) (y : TmQ Γ Y) : MetaM (TmQ.InferResult x y) := do
    withTraceNode `stx.isDefEq (myLog (f_err := fun err => return m!"TmQ.infer\n  {x.quote}\n~ {y.quote}\nERROR {err.toMessageData}") (fun ⟨T, _, _, prf⟩ => return m!"TmQ.infer\n  {x.quote}\n~ {y.quote}\n|> {T.quote}\nProof: {prf.quote}")) do
      -- The original paper does not demand that `infer` reduce terms (since they are already neutral anyway).
      -- But we reduce them, because we need to compute away substitutions.
      let ⟨X', xr, x_red_xr⟩ <- TmQ.red x
      let ⟨Y', yr, y_red_yr⟩ <- TmQ.red y
      trace[stx.isDefEq] "reduced lhs to {xr.quote}"
      trace[stx.isDefEq] "reduced rhs to {yr.quote}"
      let i <- TmQ.infer_impl xr yr
      let prf := TmHConvQ.trans (.trans x_red_xr i.conv) (.symm y_red_yr)
      return ⟨i.T, .bySorry, .bySorry, prf⟩

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
  partial def TmQ.isDefEqRed (x : TmQ Γ X) (y : TmQ Γ Y) (T : TyQ Γ) : MetaM (TmQ.IsDefEqResult x y T) := do
    -- if let some ⟨name, A, B, conv⟩ <- T.isPi then -- __negative__: Want `Γ ⊢ x ≅ₕ xy : Pi A B`, so do η-expansion
    --   sorry
    if let some ⟨conv⟩ <- T.isU then -- __NeuPos__
      let ⟨T', c1, c2, c⟩ <- TmQ.infer x y
      return ⟨.bySorry, .bySorry, c⟩
    -- match Tq with
    -- -- | ~q(Ty.Pi $A $B) => -- __negative__: Want `Γ ⊢ x₁ ≅ₕ x₂ : Pi A B`, so do η-expansion
    -- --   sorry
    -- | ~q(Ty.U) => -- __NeuPos__
    --   let S : Q(Ty $Γq) <- mkFreshExprMVarQ q(Ty $Γq)
    --   let x_conv_y : TmConvQ x y <- @TmQ.infer Γ S x y
    --   return x_conv_y
    throwError "{Expr.const `TmQ.isDefEqRed []}: Don't know how to handle\n  {x.quote}\n≅ₕ\n  {y.quote}\n<|\n  {T.quote}"

  /-- `Γ ⊢ X ≅ₕ Y <|` Reduced types are convertible. -/
  partial def TyQ.isDefEqRed (X Y : TyQ Γ) : MetaM (TyConvQ X Y) := do
    if let some ⟨convX⟩ <- X.isU then
      if let some ⟨convY⟩ <- Y.isU then
        return convX.trans convY.symm

    if let some ⟨t1, convX⟩ <- X.isEl then
      if let some ⟨t2, convY⟩ <- Y.isEl then
        let ⟨T, _, _, conv⟩ <- TmQ.infer t1 t2
        let conv : TmConvQ t1 t2 := .unsafeIntro conv.tmConv
        let c : TyConvQ (.El t1) (.El t2) := .El t1 t2 conv
        return convX |>.trans c |>.trans convY.symm

    if let some ⟨name1, A1, B1, convX⟩ <- X.isPi then
      if let some ⟨name2, A2, B2, convY⟩ <- Y.isPi then
        let Ac <- TyQ.isDefEq A1 A2
        let Bc <- TyQ.isDefEq B1 (B2.conv (.ext' Ac.symm))
        let c : TyConvQ (TyQ.Pi name1 A1 B1) (TyQ.Pi name2 A2 B2) := .bySorry -- from Ac, Bc
        return convX |>.trans c |>.trans convY.symm
    throwError m!"{Expr.const `TyQ.isDefEqRed []}: Don't know how to handle\n  {X.quote}\n≅ₕ\n  {Y.quote}"

  /-- `Γ ⊢ x ≅ y <| T` Terms are convertible at type T. -/
  partial def TmQ.isDefEq (x : TmQ Γ X) (y : TmQ Γ Y) (T : TyQ Γ) : MetaM (TmQ.IsDefEqResult x y T)  := do
    withTraceNode `stx.isDefEq (myLog (f_err := fun err => return m!"TmQ.isDefEq\n   {x.quote}\n≅ {y.quote}\n<| {T.quote}\n~~> ERROR {err.toMessageData}") (fun ⟨_, _, prf⟩ => return m!"TmQ.isDefEq\n   {x.quote}\n≅  {y.quote}\n<| {T.quote}\nProof: {prf.quote}")) do
      let ⟨X', xr, x_red_xr⟩ <- TmQ.red x
      let ⟨Y', yr, y_red_yr⟩ <- TmQ.red y
      let ⟨Tr, T_red_Tr⟩ <- TyQ.red T
      trace[stx.isDefEq] "reduced lhs to {xr.quote}"
      trace[stx.isDefEq] "reduced rhs to {yr.quote}"
      trace[stx.isDefEq] "reduced type to {Tr.quote}"
      let xr_conv_yr <- TmQ.isDefEqRed xr yr Tr
      let prf := TmHConvQ.trans (.trans x_red_xr xr_conv_yr.conv) (.symm y_red_yr)
      return ⟨.bySorry, .bySorry, prf⟩

  /-- `Γ ⊢ X ≅ Y <|` Types are convertible. -/
  partial def TyQ.isDefEq (X Y : TyQ Γ) : MetaM (TyConvQ X Y) := do
    withTraceNode `stx.isDefEq (myLog (f_err := fun err => return m!"TyQ.isDefEq\n   {X.quote}\n≅  {Y.quote}\n~~> ERROR {err.toMessageData}") (fun prf => return m!"TyQ.isDefEq\n   {X.quote}\n≅  {Y.quote}\nProof: {prf.quote}")) (do
      let ⟨Xr, X_red_Xr⟩ <- TyQ.red X
      let ⟨Yr, Y_red_Yr⟩ <- TyQ.red Y
      trace[stx.isDefEq] "reduced lhs to {Xr.quote}"
      trace[stx.isDefEq] "reduced rhs to {Yr.quote}"
      let Xr_conv_Yr <- TyQ.isDefEqRed Xr Yr
      return TyConvQ.trans (TyConvQ.trans X_red_Xr Xr_conv_Yr) (TyConvQ.symm Y_red_Yr)    )
end

/- # Elaborator
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
  partial def elabTmInferringRed (Γ : ConQ) (stx : Term) : TermElabM <| (X : TyQ Γ) × (TmQ Γ X) := withRef stx do
    let ⟨X, t⟩ <- elabTmInferring Γ stx
    let ⟨Xr, X_red_Xr⟩ <- TyQ.red X
    if <- Meta.isDefEq X Xr then return ⟨Xr, t.unsafeCast⟩ -- optimization to avoid needless `.conv`
    -- have `t : X`, but need `Tm.conv t _ : Xr`
    let t' : TmQ Γ Xr := TmQ.conv X_red_Xr t
    addTermInfo' stx t'
    return ⟨Xr, t'⟩

  /-- Elaborates term, inferring type. `Γ ⊢ stx |> X` -/
  partial def elabTmInferring (Γ : ConQ) (stx : Term) : TermElabM <| (X : TyQ Γ) × (TmQ Γ X) := withRef stx do
    -- withTraceNode `stx.elab (niceLog m! "elabTmInferring': {stx}") do
    match stx with
    | `($id:ident) =>
      let .some ⟨X, v⟩ := Γ.findVar! id.getId | throwError "elabTmInferring': No such variable {id.getId}"
      return ⟨X, .var v⟩
    | `($stx_f $stx_a) =>
      have Γq := Γ.quote
      let ⟨F, f⟩ <- elabTmInferringRed Γ stx_f -- `Γ ⊢ f |>ₕ Pi A B`
      have F : Q(Ty $Γq) := F.quote
      have f : Q(Tm $Γq $F) := f.quote
      let A : Q(Ty $Γq) <- mkFreshExprMVarQ q(Ty $Γq)
      let B : Q(Ty (.ext $Γq $A)) <- mkFreshExprMVarQ q(Ty (.ext $Γq $A))
      let _ <- assertDefEq q($F) q(@Ty.Pi $Γq $A $B) m!"(from elabTmInferring, elabing {stx})" -- assign A and B. We can assume that `F` is some `.Pi _ _`, because elabTmInferring also reduces the type for us, computing away substitutions and some other stuff.
      let a : TmQ Γ (.unsafeIntro A) <- elabTm Γ (.unsafeIntro A) stx_a -- `Γ ⊢ a <| A`
      let Ba : TyQ Γ := TyQ.subst (.unsafeIntro B) (SubstQ.apply a) -- `B[Subst.cons .id (Tm.conv a _)]`
      return ⟨Ba, TmQ.app (name := `anonymous) (.unsafeIntro f) a⟩ -- `Γ ⊢ f a |> B[⟨id, a.conv _⟩]`
    | `(fun ($stx_a:ident : $stx_A) => $stx_body)
    | `(fun  $stx_a:ident : $stx_A  => $stx_body) =>
      let name := stx_a.getId
      let A : TyQ Γ <- elabTy Γ stx_A -- `Γ ⊢ A <|`
      withLocalDeclD name A fun a_fv => do
        addTermInfo' (isBinder := true) stx_a a_fv
        let ⟨B, body⟩ <- elabTmInferringRed (.ext Γ name A) stx_body -- `Γ; A ⊢ body |> B`
        let X : TyQ Γ := TyQ.Pi name A B
        let lam : TmQ Γ X := TmQ.lam body
        addTermInfo' stx lam
        return ⟨X, lam⟩ -- therefore `Γ ⊢ fun (a : A) => body |> Pi A B`
    | `(( $stx_t:term )) => elabTmInferringRed Γ stx_t
    | _ => throwUnsupportedSyntax

  partial def elabTm (Γ : ConQ) (A : TyQ Γ) (stx : Term) : TermElabM (TmQ Γ A) := withRef stx do
    let ⟨A', t⟩ <- elabTmInferringRed Γ stx
    if <- Meta.isDefEq A' A then -- This `Meta.isDefEq` is only an optimization to avoid needless `Tm.conv`
      return t.unsafeCast
    else
      let c : @TyConvQ Γ A' A <- TyQ.isDefEq A' A
      return TmQ.conv c t
end

elab "Tm(" t:term ")" : term <= Expected => do
  let Γ : ConQ := .nil
  let X : Q(Ty .nil) <- mkFreshExprMVarQ q(Ty .nil)
  if <- isDefEq q(Tm .nil $X) Expected then
      elabTm Γ (.unsafeIntro X) t
  else throwError "Oh no"

elab "Ty(" T:term ")" : term => do
  let Γ : ConQ := .nil
  elabTy Γ T

open Notation
open Ty Tm Var Subst
set_option pp.fieldNotation.generalized false

-- set_option trace.stx.red true
-- set_option trace.stx.isQ true
set_option trace.stx.isDefEq true

#check Ty(Type)
#check Ty(Type -> Type)
#check Ty((A : Type) -> A)
#check Ty((A : Type) -> (a : A) -> A)
#check Ty((A : Type) -> (B : Type) -> (a : A) -> A)
#check (Ty( (A : Type -> Type) -> (B : Type) -> A B ) : Ty .nil)

def foo := Ty(       (A : Type -> Type) -> (B : Type) -> A B        )
-- set_option pp.all true in -- very spammy
#print foo

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
