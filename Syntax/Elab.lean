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

/-
  # Quotation Helpers
-/

inductive ConQ where
| nil : ConQ
| ext : ConQ -> Name -> Expr -> ConQ
def TyQ (Γ : ConQ) : Type := Expr
def TmQ (Γ : ConQ) (A : TyQ Γ) : Type := Expr
def VarQ (Γ : ConQ) : Type := Nat
def SubstQ (Γ Δ : ConQ) : Type := Expr
def ConConvQ (Γ Δ : ConQ) : Type := Expr
def TyConvQ {Γ : ConQ} (X Y : TyQ Γ) : Type := Expr
def TmConvQ {Γ : ConQ} {A : TyQ Γ} (x y : TmQ Γ A) : Type := Expr

def ConQ.quote : ConQ -> Q(Con)
| .nil => q(Con.nil)
| .ext Γq name Aq =>
  let Aq : TyQ Γq := Aq
  let Γexpr : Q(Con) := Γq.quote
  .app q(Con.ext $Γexpr) Aq
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
def TyConvQ.quote {Γ : ConQ} {X Y : TyQ Γ} (c : TyConvQ X Y) :
  have Γ : Q(Con) := Γ.quote
  have X : Q(Ty $Γ) := X.quote
  have Y : Q(Ty $Γ) := Y.quote
  Q(TyConv $X $Y)
  := c

instance : ToExpr ConQ where
  toTypeExpr := q(Con)
  toExpr := ConQ.quote
instance : ToExpr (TyQ Γ) where
  toTypeExpr := q(Ty $Γ.quote)
  toExpr := TyQ.quote

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

def TmQ.app (f : TmQ Γ (.Pi name A B)) (a : TmQ Γ A) : TmQ Γ (TyQ.subst B (.apply a))
  := mkAppN q(@Tm.app) #[ Γ.quote, A.quote, B.quote, f.quote, a.quote ]

def TmQ.lam {Γ name} {A : TyQ Γ} {B : TyQ (.ext Γ name A)} (body : TmQ (.ext Γ name A) B) : TmQ Γ (TyQ.Pi name A B)
  := mkAppN q(@Tm.lam) #[ Γ.quote, A.quote, B.quote, body.quote ]

def TmQ.conv {Γ : ConQ} {X Y : TyQ Γ} (c : TyConvQ X Y) (t : TmQ Γ X) : TmQ Γ Y :=
  mkAppN q(@Tm.conv) #[Γ.quote, X.quote, Y.quote, c.quote, t.quote]

def ConQ.findVar (n : Name) : (Γ : ConQ) -> Option (VarQ Γ)
| .nil => none
| .ext Γ name _ => if n = name then some .zero else (Γ.findVar n).map Nat.succ

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

def TyConvQ.refl (X : TyQ Γ) : TyConvQ X X :=
  let Xq := X.quote
  q((TyConv.refl : TyConv $Xq $Xq))
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

/-
  # Reduction

  For now, we use Quote4's `| ~q(..) => ...` to match on expressions, but this is overkill and
  has performance issues. I worry it might accidentally unfold too much while checking defeq.
  Instead, `match_expr` would be more performant and would not unfold exprs, but also a pain to write.

  It might also be helpful to have a dedicated reduction relation, instead of piggybacking on TyConv.
-/

partial def TyQ.red {Γ : ConQ} (X : TyQ Γ) : MetaM <| (Y : TyQ Γ) × TyConvQ X Y := do
  have Γq : Q(Con) := Γ.quote
  have Xq : Q(Ty $Γq) := X
  let cont (Y : TyQ Γ) (X_red_Y : TyConvQ X Y) : MetaM <| (Z : TyQ Γ) × TyConvQ X Z := do
    let ⟨Z, Y_red_Z⟩ <- TyQ.red Y
    let X_red_Z := TyConvQ.trans (X := X) X_red_Y Y_red_Z
    return ⟨Z, X_red_Z⟩
  match Xq with
  | ~q(Ty.subst (Ty.subst $A $σ1) $σ2) => -- `A[σ1][σ2] = A[σ1 ∘ σ2]`
    let Y : Q(Ty $Γq) := q(Ty.subst $A (Subst.comp $σ1 $σ2))
    let X_red_Y : Q(TyConv $Xq $Y) := q(TyConv.ofEq Ty.subst_comp)
    cont Y X_red_Y
  | ~q(Ty.subst .U $σ) => -- `U[σ] ≡ U`
    let Y : Q(Ty $Γq) := q(.U)
    return ⟨Y, .refl X⟩
  | ~q(Ty.subst (.El $t) $σ) => -- `(.El t)[σ] ≡ El t[σ]`
    let Y : Q(Ty $Γq) := q(Ty.El (Tm.subst $t $σ))
    cont Y (.refl X)
  | ~q(Ty.subst (.Pi $A $B) $σ) => -- `(.Pi A B)[σ] ≡ Pi A[σ] B[lift σ]`
    let Y : Q(Ty $Γq) := q(Ty.Pi (.subst $A $σ) (Ty.subst $B (.lift $σ)))
    cont Y (.refl X)
  | _ => return ⟨Xq, .refl X⟩ -- no-op

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

/-
  # Typed Algorithmic Conversion Checking
-/

mutual
  /-- `Γ ⊢ t ~ t' |> T`. The `out_T` here is an output, and should be a metavariable. -/
  partial def TmQ.infer (out_T : TyQ Γ) (x y : TmQ Γ out_T) : MetaM (TmConvQ x y) :=
    sorry

  /-- `Γ ⊢ x ≅ y <| T` -/
  partial def TmQ.isDefEq (T : TyQ Γ) (x y : TmQ Γ T) : MetaM (TmConvQ x y) :=
    sorry

  /-- `Γ ⊢ X ≅ Y <|` -/
  partial def TyQ.isDefEq (X Y : TyQ Γ) : MetaM (TyConvQ X Y) :=
    sorry
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
      let c : @TyConvQ Γ A' A := q((sorry : TyConv $A'.quote $A.quote)) -- todo: try finding conversion proof
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
