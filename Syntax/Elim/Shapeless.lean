import Lean
import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Data.Multiset.FinsetOps
import Mathlib.Data.Multiset.AddSub
import Syntax.AllTogether
import Syntax.Elim.Cases
import Syntax.Util.Multiset
import Aesop
import Qq

set_option pp.fieldNotation.generalized false
set_option linter.unusedVariables false
set_option pp.proofs true
open DershowitzManna.Notation
open Relation (TransGen)
attribute [-simp] Multiset.insert_eq_cons


structure MotivesL where
  ConM : Con -> Sort u
  TyM  : (Γ : Con) -> (A : Ty Γ) -> Sort u
  TmM  : (Γ : Con) -> (A : Ty Γ) -> Tm Γ A -> Sort u
  VarM : (Γ : Con) -> (A : Ty Γ) -> Var Γ A -> Sort u
  TmM_conv  : (Γ : Con) -> (X Y : Ty Γ) -> (t : Tm  Γ X) -> (Xc : TyConv X Y) -> TmM  Γ X t = TmM  Γ Y (t.conv Xc)

structure MethodsL extends MotivesL where
  nilM : ConM .nil
  extM : (Γ : Con) -> (Γd : ConM Γ) -> (A : Ty Γ) -> (Ad : TyM Γ A) -> ConM (.ext Γ A)
  UM : (Γ : Con) -> (Γd : ConM Γ) -> TyM Γ .U
  PiM :
    (Γ : Con) -> (Γd : ConM Γ) ->
    (A : Ty Γ) -> (Ad : TyM Γ A) ->
    (B : Ty (Γ.ext A)) -> (Bd : TyM (.ext Γ A) B) ->
    TyM Γ (.Pi A B)
  ElM :
    (Γ : Con) -> (Γd : ConM Γ) ->
    (t : Tm Γ .U) -> (td : TmM Γ .U t) ->
    TyM Γ (.El t)
  SumM :
    (Γ : Con) -> (Γd : ConM Γ) ->
    (A : Ty Γ) -> (Ad : TyM Γ A) ->
    (B : Ty Γ) -> (Bd : TyM Γ B) ->
    TyM Γ (.Sum A B)
  UnitM :
    (Γ : Con) -> (Γd : ConM Γ) -> TyM Γ (.Unit)
  vzM : (Γ : Con) -> (Γd : ConM Γ) -> (A : Ty Γ) -> (Ad : TyM Γ A) -> VarM (.ext Γ A) (A.subst .wki) .vz
  vsM : (Γ : Con) -> (Γd : ConM Γ) -> (A : Ty Γ) -> (Ad : TyM Γ A) -> (B : Ty Γ) -> (Bd : TyM Γ B) -> (v : Var Γ A) -> (vd : VarM Γ A v) -> VarM (.ext Γ B) (A.subst .wki) (.vs v)
  varM : (Γ : Con) -> (Γd : ConM Γ) -> (A : Ty Γ) -> (Ad : TyM Γ A) -> (v : Var Γ A) -> (vd : VarM Γ A v) -> TmM Γ A (.var v)
  appM :
    (Γ : Con) -> (Γd : ConM Γ) ->
    (A : Ty Γ) -> (Ad : TyM Γ A) ->
    (B : Ty (Γ.ext A)) -> (Bd : TyM (.ext Γ A) B) ->
    (f : Tm Γ (.Pi A B)) -> (fd : TmM Γ (.Pi A B) f) ->
    (a : Tm Γ A) -> (ad : TmM Γ A a) ->
    TmM Γ (B.subst (.apply a))   (.app f a)
  lamM :
    (Γ : Con) -> (Γd : ConM Γ) ->
    (A : Ty Γ) -> (Ad : TyM Γ A) ->
    (B : Ty (Γ.ext A)) -> (Bd : TyM (.ext Γ A) B) ->
    (b : Tm (.ext Γ A) B) -> (bd : TmM (.ext Γ A) B b) ->
    TmM Γ (.Pi A B) (.lam b)
  piM  :
    (Γ : Con) -> (Γd : ConM Γ) ->
    (a : Tm Γ .U) -> (ad : TmM Γ .U a) ->
    (b : Tm (.ext Γ (.El a)) .U) -> (bd : TmM (.ext Γ (.El a)) .U b) ->
    TmM Γ .U (.pi a b)
  unitM :
    (Γ : Con) -> (Γd : ConM Γ) ->
    TmM Γ .Unit .unit

section Termination

mutual
  @[simp] abbrev ConE.size' : ConE γ -> Nat
  | .nil => 1
  | .ext Γ A => 1 + Γ.size' + A.size'

  @[simp] abbrev TyE.size' : TyE γ -> Nat
  | .U => 1
  | .Pi A B => 1 + A.size' + B.size'
  | .El t => 1 + t.size'
  | .Sum A B => 1 + A.size' + B.size'
  | .Unit => 1

  @[simp] abbrev VarE.size' : VarE γ -> Nat
  | .vz => 1
  | .vs v => 1 + v.size'

  @[simp] abbrev TmE.size' : TmE γ -> Nat
  | .var v => 1 + v.size'
  | .lam A B body => 1 + A.size' + B.size' + body.size'
  | .app A B f a => 1 + A.size' + B.size' + f.size' + a.size'
  | .pi A B => 1 + (1 + A.size') + (1 + B.size') -- `size (.El A) = (1 + size A)`
  | .elimSum A B Mot lM rM t => 1 + A.size' + B.size' + Mot.size' + lM.size' + rM.size' + t.size'
  | .left t => 1 + t.size'
  | .right t => 1 + t.size'
  | .unit => 1
end


inductive ConTyTmE : Type
| con (Γ : ConE γ) : ConTyTmE
| ty (Γ : ConE γ) (A : TyE γ) : ConTyTmE
| tm (Γ : ConE γ) (A : TyE γ) (t : TmE γ) : ConTyTmE

@[simp] noncomputable abbrev ConTyTmE.size'1 : ConTyTmE -> Nat
| .con Γ => Γ.size'
| .ty Γ A => Γ.size' + A.size'
| .tm Γ A t => Γ.size' + A.size' + t.size'
@[simp] noncomputable abbrev ConTyTmE.size'2 : ConTyTmE -> Nat
| .con Γ => Γ.size'
| .ty Γ A => 2 + A.size' -- thank you Kenji
| .tm Γ A t => 1 + t.size'


@[aesop safe constructors]
inductive ConTyTmE.LT' : ConTyTmE -> ConTyTmE -> Prop
| extTail : LT' (.con Γ)  (.con (.ext Γ A))
| extHead : LT' (.ty Γ A) (.con (.ext Γ A))
| TyCon    : LT' (.con Γ)           (.ty Γ A)
| PiDom    : LT' (.ty Γ A)          (.ty Γ (.Pi A B))
| PiCod    : LT' (.ty (.ext Γ A) B) (.ty Γ (.Pi A B))
| SumLeft  : LT' (.ty Γ A)          (.ty Γ (.Sum A B))
| SumRight : LT' (.ty Γ B)          (.ty Γ (.Sum A B))
| ElU      : LT' (.ty Γ .U)         (.ty Γ (.El T))
| ElTerm   : LT' (.tm Γ .U T)       (.ty Γ (.El T))
| TmCon   : LT' (.con Γ)                    (.tm Γ A t)
| TmTy    : LT' (.ty Γ A)                   (.tm Γ A t)
| appDom  : LT' (.ty Γ A)                   (.tm Γ (B.subst (.cons .id a)) (.app A B f a))
| appCod  : LT' (.ty (.ext Γ A) B)          (.tm Γ (B.subst (.cons .id a)) (.app A B f a))
| appFn   : LT' (.tm Γ (.Pi A B) f)         (.tm Γ (B.subst (.cons .id a)) (.app A B f a))
| appArg  : LT' (.tm Γ A a)                 (.tm Γ (B.subst (.cons .id a)) (.app A B f a))
| lamDom  : LT' (.ty Γ A)                   (.tm Γ (.Pi A B) (.lam A B body))
| lamCod  : LT' (.ty (.ext Γ A) B)          (.tm Γ (.Pi A B) (.lam A B body))
| lamBody : LT' (.tm (.ext Γ A) B body)     (.tm Γ (.Pi A B) (.lam A B body))
| piDom   : LT' (.tm Γ .U A)                (.tm Γ .U (.pi A B))
| piCod   : LT' (.tm (.ext Γ (.El A)) .U B) (.tm Γ .U (.pi A B))
| left          : LT' (.tm Γ A a)           (.tm Γ (.Sum A B) (.left a))
| right         : LT' (.tm Γ B b)           (.tm Γ (.Sum A B) (.right b))
| elimSumMot    : LT' (.ty (.ext Γ (.Sum A B)) Mot                                            ) (.tm Γ (Mot.subst (.cons .id t)) (.elimSum A B Mot lM rM t))
| elimSumLeftM  : LT' (.tm (.ext Γ A         ) (Mot.subst (.cons .wki (.left  (.var .vz)))) lM) (.tm Γ (Mot.subst (.cons .id t)) (.elimSum A B Mot lM rM t))
| elimSumRightM : LT' (.tm (.ext Γ B         ) (Mot.subst (.cons .wki (.right (.var .vz)))) rM) (.tm Γ (Mot.subst (.cons .id t)) (.elimSum A B Mot lM rM t))
| elimSumTarget : LT' (.tm Γ                   (.Sum A B)                                   t ) (.tm Γ (Mot.subst (.cons .id t)) (.elimSum A B Mot lM rM t))

@[grind! .] theorem TyE.size'Of_pos {A : TyE γ} : sizeOf A > 0 := by
  cases A <;> dsimp [sizeOf] <;> omega

@[grind! .] theorem TmE.size'_pos {t : TmE γ} : t.size' > 0 := by
  cases t <;> dsimp [TmE.size'] <;> omega

@[grind! .] theorem TyE.size'_pos {A : TyE γ} : A.size' > 0 := by
  cases A <;> dsimp [TyE.size'] <;> grind

@[aesop safe apply] theorem Prod.Lex.cases {a b c d : Nat} : (a < c) ∨ (a = c ∧ b < d) -> Prod.Lex (. < .) (. < .) (a, b) (c, d) := by omega

set_option maxHeartbeats 2000000

theorem ConTyTmE.acc (x : ConTyTmE) : Acc LT' x :=
  Acc.intro x fun y (hy : LT' y x) => -- ⊢ `Acc y`
    match x with
    | @ConTyTmE.con 0 .nil => nomatch hy
    | @ConTyTmE.con (g+1) (.ext Γ A) => match hy with
      | .extTail => ConTyTmE.acc (.con Γ)
      | .extHead => ConTyTmE.acc (.ty Γ A)
    | @ConTyTmE.ty g Γ (.U) => match hy with
      | .TyCon => ConTyTmE.acc (.con Γ)
    | @ConTyTmE.ty g Γ (.Unit) => match hy with
      | .TyCon => ConTyTmE.acc (.con Γ)
    | @ConTyTmE.ty g Γ (.Pi A B) => match hy with
      | .TyCon => ConTyTmE.acc (.con Γ)
      | .PiDom => ConTyTmE.acc (.ty Γ A)
      | .PiCod => ConTyTmE.acc (.ty (.ext Γ A) B)
    | @ConTyTmE.ty g Γ (.El t) => match hy with
      | .TyCon => acc _
      | .ElTerm => acc _
      | .ElU => acc _
    | @ConTyTmE.ty g Γ (.Sum A B) => match hy with
      | .TyCon => acc _
      | .SumLeft => acc _
      | .SumRight => acc _
    | @ConTyTmE.tm g Γ X (.app A B f a) => match hy with
      | .TmCon => acc _
      | @LT'.TmTy _ _ _ _ => acc _
      | @LT'.appArg _ _ _ _ _ _ => acc _
      | @LT'.appFn _ _ _ _ _ _ => acc _
      | @LT'.appCod _ _ _ _ _ _ => acc _
      | @LT'.appDom _ _ _ _ _ _ => acc _
    | @ConTyTmE.tm g Γ X (.var v) => sorry
    | @ConTyTmE.tm g Γ X (.lam A B body) => match hy with
      | .TmCon => acc _
      | .TmTy => acc _
      | .lamDom => acc _
      | .lamCod => acc _
      | .lamBody => acc _
    | @ConTyTmE.tm g Γ X (.pi A B) => match hy with
      | .TmCon => acc _
      | .TmTy => acc _
      | .piDom => acc _
      | .piCod => acc _
    | @ConTyTmE.tm g Γ X (.left a) => match hy with
      | .TmCon => acc _
      | .TmTy => acc _
      | .left => acc _
    | @ConTyTmE.tm g Γ X (.right b) => match hy with
      | .TmCon => acc _
      | .TmTy => acc _
      | .right => acc _
    | @ConTyTmE.tm g Γ X (.elimSum A B Mot lM rM t) => match hy with
      | .TmCon => acc _
      | .TmTy => acc _
      | .elimSumMot => acc _
      | .elimSumLeftM => acc _
      | .elimSumRightM => acc _
      | .elimSumTarget => acc _
    | @ConTyTmE.tm g Γ X (.unit) => match hy with
      | .TmCon => acc _
      | .TmTy => acc _
  termination_by (size'1 x, size'2 x)
  decreasing_by --all_goals sorry
    all_goals apply Prod.Lex.cases
    . grind?
    . grind?
    . rw [size'1, size'1]
      grind?
    . grind?
    . grind?
    . grind?
    . rw [size'1, size'1]
      grind?
    . rw [size'1, size'1]
      grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . grind?
    . sorry
    . sorry
    . grind?
    . grind?
    . grind?
    done

theorem ConTyTmE.LT'.wellFounded : WellFounded LT' :=
  WellFounded.intro fun (x : ConTyTmE) =>
    ConTyTmE.acc x

-- Now, let's build the transitive closure of the above relation. This is easy thanks to TransGen.

def ConTyTmE.LT := TransGen LT'
def ConTyTmE.LT.extTail : LT (.con Γ)  (.con (.ext Γ A))    := TransGen.single .extTail
def ConTyTmE.LT.extHead : LT (.ty Γ A) (.con (.ext Γ A))    := TransGen.single .extHead
def ConTyTmE.LT.TyCon    : LT (.con Γ)           (.ty Γ A)    := TransGen.single .TyCon
def ConTyTmE.LT.PiDom    : LT (.ty Γ A)          (.ty Γ (.Pi A B))    := TransGen.single .PiDom
def ConTyTmE.LT.PiCod    : LT (.ty (.ext Γ A) B) (.ty Γ (.Pi A B))    := TransGen.single .PiCod
def ConTyTmE.LT.SumLeft  : LT (.ty Γ A)          (.ty Γ (.Sum A B))    := TransGen.single .SumLeft
def ConTyTmE.LT.SumRight : LT (.ty Γ B)          (.ty Γ (.Sum A B))    := TransGen.single .SumRight
def ConTyTmE.LT.ElTerm   : LT (.tm Γ .U T)       (.ty Γ (.El T))    := TransGen.single .ElTerm
def ConTyTmE.LT.TmCon   : LT (.con Γ)                    (.tm Γ A t)    := TransGen.single .TmCon
def ConTyTmE.LT.TmTy    : LT (.ty Γ A)                   (.tm Γ A t)    := TransGen.single .TmTy
def ConTyTmE.LT.appDom  : LT (.ty Γ A)                   (.tm Γ (B.subst (.cons .id a)) (.app A B f a))    := TransGen.single .appDom
def ConTyTmE.LT.appCod  : LT (.ty (.ext Γ A) B)          (.tm Γ (B.subst (.cons .id a)) (.app A B f a))    := TransGen.single .appCod
def ConTyTmE.LT.appFn   : LT (.tm Γ (.Pi A B) f)         (.tm Γ (B.subst (.cons .id a)) (.app A B f a))    := TransGen.single .appFn
def ConTyTmE.LT.appArg  : LT (.tm Γ A a)                 (.tm Γ (B.subst (.cons .id a)) (.app A B f a))    := TransGen.single .appArg
def ConTyTmE.LT.lamDom  : LT (.ty Γ A)                   (.tm Γ (.Pi A B) (.lam A B body))    := TransGen.single .lamDom
def ConTyTmE.LT.lamCod  : LT (.ty (.ext Γ A) B)          (.tm Γ (.Pi A B) (.lam A B body))    := TransGen.single .lamCod
def ConTyTmE.LT.lamBody : LT (.tm (.ext Γ A) B body)     (.tm Γ (.Pi A B) (.lam A B body))    := TransGen.single .lamBody
def ConTyTmE.LT.piDom   : LT (.tm Γ .U A)                (.tm Γ .U (.pi A B))    := TransGen.single .piDom
def ConTyTmE.LT.piCod   : LT (.tm (.ext Γ (.El A)) .U B) (.tm Γ .U (.pi A B))    := TransGen.single .piCod
def ConTyTmE.LT.left          : LT (.tm Γ A a)           (.tm Γ (.Sum A B) (.left a))    := TransGen.single .left
def ConTyTmE.LT.right         : LT (.tm Γ B b)           (.tm Γ (.Sum A B) (.right b))    := TransGen.single .right
def ConTyTmE.LT.elimSumMot    : LT (.ty (.ext Γ (.Sum A B)) Mot                                            ) (.tm Γ (Mot.subst (.cons .id t)) (.elimSum A B Mot lM rM t))    := TransGen.single .elimSumMot
def ConTyTmE.LT.elimSumLeftM  : LT (.tm (.ext Γ A         ) (Mot.subst (.cons .wki (.left  (.var .vz)))) lM) (.tm Γ (Mot.subst (.cons .id t)) (.elimSum A B Mot lM rM t))    := TransGen.single .elimSumLeftM
def ConTyTmE.LT.elimSumRightM : LT (.tm (.ext Γ B         ) (Mot.subst (.cons .wki (.right (.var .vz)))) rM) (.tm Γ (Mot.subst (.cons .id t)) (.elimSum A B Mot lM rM t))    := TransGen.single .elimSumRightM
def ConTyTmE.LT.elimSumTarget : LT (.tm Γ                   (.Sum A B)                                   t ) (.tm Γ (Mot.subst (.cons .id t)) (.elimSum A B Mot lM rM t))    := TransGen.single .elimSumTarget

instance : LT ConTyTmE := ⟨ConTyTmE.LT⟩
instance : LE ConTyTmE := ⟨fun x y => ConTyTmE.LT x y ∨ x = y⟩
theorem ConTyTmE.LT.wellFounded : WellFounded LT := WellFounded.transGen ConTyTmE.LT'.wellFounded
instance : WellFoundedLT ConTyTmE := ⟨ConTyTmE.LT.wellFounded⟩
instance : Preorder ConTyTmE where
  lt := ConTyTmE.LT
  le_refl x := .inr (.refl x)
  le_trans x y z h1 h2 :=
    match h1, h2 with
    | .inl lt1, .inl lt2 => .inl <| TransGen.trans lt1 lt2
    | .inr (.refl _), .inl lt2 => .inl lt2
    | .inl lt1, .inr (.refl _) => .inl lt1
    | .inr (.refl _), .inr (.refl _) => .inr (.refl _)
  lt_iff_le_not_ge a b := by
    constructor
    . intro lt
      sorry
    . intro ⟨l, r⟩
      sorry

/-- info: Multiset.instWellFoundedIsDershowitzMannaLT -/
#guard_msgs in #synth WellFoundedRelation (Multiset ConTyTmE)

@[aesop unsafe] theorem DM.test1 : {ConTyTmE.con Γ} << {.con Γ, .ty Γ A} := by exact DershowitzManna.proj_2_1
@[aesop unsafe] theorem DM.test2 : {ConTyTmE.ty Γ A} << {.ty Γ (.Pi A B)} := by apply DershowitzManna.lift_lt; exact .PiDom
@[aesop unsafe] theorem DM.test3 : {ConTyTmE.ty Γ A, ConTyTmE.ty (.ext Γ A) B} << {.ty Γ (.Pi A B)} := DershowitzManna.lift_lt_2 .PiDom .PiCod
@[aesop unsafe] theorem DM.test4 : {.con Γ, ConTyTmE.ty Γ A} << {.con Γ, .ty Γ (.Pi A B)} := by exact DershowitzManna.shave {.con Γ} test2
@[aesop unsafe] theorem DM.test5 : {.con Γ, ConTyTmE.ty Γ A, ConTyTmE.ty (.ext Γ A) B} << {.con Γ, .ty Γ (.Pi A B)} := by exact DershowitzManna.shave {ConTyTmE.con Γ} (DershowitzManna.lift_lt_2 .PiDom .PiCod)

end Termination


set_option pp.letVarTypes true
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open DershowitzManna in
mutual
  def Con.recL' (m : MethodsL) (Γe : ConE γ) (Γw : ConW Γe) : m.ConM ⟨γ, Γe, Γw⟩ :=
    match γ, Γe with
    | .zero, .nil => m.nilM
    | .succ γ, .ext Γe Ae =>
      m.extM ⟨γ, Γe, Γw.ext_Γw⟩ (Con.recL' m Γe Γw.ext_Γw) ⟨Ae, Γw.ext_Aw⟩ (Ty.recL' m Ae Γw.ext_Aw)
  termination_by ({ .con Γe } : Multiset ConTyTmE)
  decreasing_by
    . exact lift_lt .extTail
    . exact lift_lt_2 .extTail .extHead

  def Ty.recL' (m : MethodsL) {Γe : ConE γ} {Γw : ConW Γe} (Xe : TyE γ) (Xw : TyW Γe Xe) : m.TyM ⟨γ, Γe, Γw⟩ ⟨Xe, Xw⟩ :=
    match Xe with
    | .U => m.UM ⟨γ, Γe, Γw⟩ (Con.recL' m Γe Γw)
    | .Pi Ae Be =>
      let Aw := Xw.Pi_Aw
      let Bw := Xw.Pi_Bw
      m.PiM ⟨γ, Γe, Γw⟩ (Con.recL' m Γe Γw) ⟨Ae, Aw⟩ (Ty.recL' m Ae Aw) ⟨Be, Bw⟩ (Ty.recL' m Be Bw)
    | .El te =>
      let tw := Xw.El_tw
      m.ElM ⟨γ, Γe, Γw⟩ (Con.recL' m Γe Γw) ⟨te, tw⟩ (Tm.recL' m te tw)
    | .Sum Ae Be =>
      let ⟨Aw, Bw⟩ := Xw.Sum_wf
      m.SumM ⟨γ, Γe, Γw⟩ (Con.recL' m Γe Γw) ⟨Ae, Aw⟩ (Ty.recL' m Ae Aw) ⟨Be, Bw⟩ (Ty.recL' m Be Bw)
    | .Unit => m.UnitM ⟨γ, Γe, Γw⟩ (Con.recL' m Γe Γw)
  termination_by ({ .con Γe, .ty Γe Xe } : Multiset ConTyTmE)
  decreasing_by
    . exact DershowitzManna.proj_2_1
    . exact DershowitzManna.proj_2_1
    . exact DM.test4
    . calc {ConTyTmE.con (.ext Γe Ae), .ty (.ext Γe Ae) Be} -- three sorries below are easy
        _ << {.ty (.ext Γe Ae) Be, .ty (.ext Γe Ae) Be} := by sorry
        _ << {.ty Γe (TyE.Pi Ae Be)} := by sorry
        _ << {.con Γe, ConTyTmE.ty Γe (TyE.Pi Ae Be)} := by sorry
    . apply DershowitzManna.proj_2_1
    . calc {ConTyTmE.con Γe, .ty Γe TyE.U, .tm Γe TyE.U te}
        _ << {.con Γe, .ty Γe (.El te)} := sorry -- from .ElU, .ElTerm
    . apply DershowitzManna.proj_2_1
    . sorry -- easy
    . sorry -- easy
    . sorry -- easy

  def Tm.recL' (m : MethodsL) {Γe : ConE γ} {Γw : ConW Γe} {Xe : TyE γ} {Xw : TyW Γe Xe} (te : TmE γ) (tw : TmW Γe Xe te) : m.TmM ⟨γ, Γe, Γw⟩ ⟨Xe, Xw⟩ ⟨te, tw⟩ :=
    match te with
    | .var ve =>
      let vw := TmW.var_wf tw
      -- let X := ve.getType Γ
      m.varM ⟨γ, Γe, Γw⟩ (Con.recL' m Γe Γw) ⟨Xe, Xw⟩ (Ty.recL' m Xe Xw) ⟨ve, vw⟩ (Var.recL' m ve vw)
    | .lam Ae Be bodye => by
      let ⟨Aw, Bw, bodyw⟩ := tw.lam_wf
      have Xc : @TyConv ⟨γ, Γe, Γw⟩ ⟨Xe, Xw⟩ (.Pi ⟨Ae, Aw⟩ ⟨Be, Bw⟩) := TmW.lam_inv tw
      let ret : m.TmM ⟨γ, Γe, Γw⟩ (.Pi ⟨Ae, Aw⟩ ⟨Be, Bw⟩) (.lam ⟨bodye, bodyw⟩) :=
        m.lamM ⟨γ, Γe, Γw⟩ (Con.recL' m Γe Γw) ⟨Ae, Aw⟩ (Ty.recL' m Ae Aw) ⟨Be, Bw⟩ (Ty.recL' m Be Bw) ⟨bodye, bodyw⟩ (Tm.recL' m bodye bodyw)
      exact m.TmM_conv _ _ _ _ Xc ▸ ret
    | .app Ae Be fe ae =>
      let ⟨Aw, Bw, fw, aw⟩ := tw.app_wf
      let ret := m.appM ⟨γ, Γe, Γw⟩ (Con.recL' m Γe Γw) ⟨Ae, Aw⟩ (Ty.recL' m Ae Aw) ⟨Be, Bw⟩ (Ty.recL' m Be Bw) ⟨fe, fw⟩ (Tm.recL' m fe fw) _ (Tm.recL' m ae aw)
      have Xc : @TyConv ⟨γ, Γe, Γw⟩ ⟨Xe, Xw⟩ (Ty.subst ⟨Be, Bw⟩ (.apply ⟨ae, aw⟩)) := TmW.app_inv tw
      m.TmM_conv _ _ _ _  Xc ▸ ret
    | .pi Ae Be =>
      let ⟨Aw, Bw⟩ := tw.pi_wf
      let ret := m.piM ⟨γ, Γe, Γw⟩ (Con.recL' m Γe Γw) ⟨Ae, Aw⟩ (Tm.recL' m Ae Aw) ⟨Be, Bw⟩ (Tm.recL' m Be Bw)
      have Xc : @TyConv ⟨γ, Γe, Γw⟩ ⟨Xe, Xw⟩ .U := tw.pi_inv
      m.TmM_conv _ _ _ _  Xc ▸ ret
    | .left .. => sorry
    | .right .. => sorry
    | .elimSum .. => sorry
    | .unit =>
      have Xc : @TyConv ⟨γ, Γe, Γw⟩ ⟨Xe, Xw⟩ .Unit := tw.unit_inv
      m.TmM_conv _ _ _ _ Xc ▸ m.unitM ⟨γ, Γe, Γw⟩ (Con.recL' m Γe Γw)
  termination_by ({ .con Γe, .ty Γe Xe, .tm Γe Xe te } : Multiset ConTyTmE)
  decreasing_by all_goals sorry

  def Var.recL' (d : MethodsL) {Γe : ConE γ} {Γw : ConW Γe} {Xe : TyE γ} {Xw : TyW Γe Xe} (ve : VarE γ) (vw : VarW Γe Xe ve) : d.VarM ⟨γ, Γe, Γw⟩ ⟨Xe, Xw⟩ ⟨ve, vw⟩ :=
    let γ + 1 := γ
    let .ext Γe Be := Γe
    let Bw := Γw.ext_Aw
    let Γw := Γw.ext_Γw
    match ve with
    | .vz => -- have `vz : Var (Γ; B) B[wki]`, where `X ≅ B[wki]`
      have Xc : Xe = Be.subst .wki := VarW.inv vw
      let ret := d.vzM ⟨γ, Γe, Γw⟩ (Con.recL' d Γe Γw) ⟨Be, Bw⟩ (Ty.recL' d Be Bw)
      Xc ▸ ret
    | .vs ve => -- have `.vs v : Var (Γ; B) A[wki]`, where `X ≅ A[wki]` and `v : Var Γ A`
      let Ae := ve.getType Γe
      have Xc : Xe = (ve.getType Γe).subst .wki := VarW.inv vw
      have vw : VarW Γe Ae ve := VarW.vs_wf vw
      have Aw : TyW Γe Ae := vw.ty_wf
      let ret := d.vsM ⟨γ, Γe, Γw⟩ (Con.recL' d Γe Γw) ⟨Ae, Aw⟩ (Ty.recL' d Ae Aw) ⟨Be, Bw⟩ (Ty.recL' d Be Bw) ⟨ve, vw⟩ (Var.recL' d ve vw)
      Xc ▸ ret -- actual `Eq.rec`, and not by conversion
  termination_by ({.con Γe, .ty Γe Xe, .tm Γe Xe (.var ve)} : Multiset ConTyTmE) -- todo add `ConTyTmE.var`
  decreasing_by all_goals sorry
end

section Iota'
  set_option allowUnsafeReducibility true
  -- set_option backward.isDefEq.respectTransparency false
  set_option maxRecDepth 7000

  /- # Iota rules
    As far as I can tell, these are theoretically definitional equalities. But Lean runs out of stack space.
  -/

  variable (m : MethodsL)
  variable {γ : Nat} (Γe : ConE γ) (Γw : ConW Γe)
  variable (Ae : TyE γ) (Aw : TyW Γe Ae)
  variable (Be : TyE (.succ γ)) (Bw : TyW (.ext Γe Ae) Be)

  def Con.nil_iota' : Con.recL' m .nil .nil = m.nilM := by rw [Con.recL']
  def Con.ext_iota' : Con.recL' m (.ext Γe Ae) (.ext Γw Aw) = m.extM ⟨γ, Γe, Γw⟩ (Con.recL' m Γe Γw) ⟨Ae, Aw⟩ (Ty.recL' m Ae Aw)
    := by rw [Con.recL'.eq_2]
  attribute [irreducible] Con.recL'

  def Ty.U_iota' : Ty.recL' m .U (.U Γw) = m.UM ⟨γ, Γe, Γw⟩ (Con.recL' m Γe Γw) := by rw [Ty.recL']
  def Ty.El_iota' : Ty.recL' m (.El te) (.El Γw tw) = m.ElM ⟨γ, Γe, Γw⟩ (Con.recL' m Γe Γw) ⟨te, tw⟩ (Tm.recL' m te tw)
    := by rw [Ty.recL'.eq_3]
  def Ty.Pi_iota' : Ty.recL' m (.Pi Ae Be) (.Pi Γw Aw Bw)
    = m.PiM ⟨γ, Γe, Γw⟩ (Con.recL' m Γe Γw) ⟨Ae, Aw⟩ (Ty.recL' m Ae Aw) ⟨Be, Bw⟩ (Ty.recL' m Be Bw)
    := by rw [Ty.recL'.eq_2]
  attribute [irreducible] Ty.recL'

  def Tm.var_iota' : Tm.recL' m (.var ve) (.var Γw Aw vw)
    = m.varM ⟨γ, Γe, Γw⟩ (Con.recL' m Γe Γw) ⟨Ae, Aw⟩ (Ty.recL' m Ae Aw) ⟨Be, Bw⟩ (Ty.recL' m Be Bw)
    := by rw [Ty.recL'.eq_2]

  attribute [irreducible] Tm.recL'
  attribute [irreducible] Var.recL'
end Iota'

section Iota
  /- And now some convenience helpers.  -/

  variable (m : MethodsL) (Γ : Con) (A : Ty Γ) (B : Ty (.ext Γ A))

  def Con.recL (m : MethodsL) (Γ : Con) : m.ConM Γ := Con.recL' (γ := Γ.1) m Γ.2.1 Γ.2.2
  def Ty.recL (m : MethodsL) {Γ : Con} (A : Ty Γ) : m.TyM Γ A := Ty.recL' m A.1 A.2
  def Tm.recL (m : MethodsL) {Γ : Con} {A : Ty Γ} (t : Tm Γ A) : m.TmM Γ A t := Tm.recL' m t.1 t.2
  def Var.recL (m : MethodsL) {Γ : Con} {A : Ty Γ} (v : Var Γ A) : m.VarM Γ A v := Var.recL' m v.1 v.2

  def Con.nil_iota : Con.recL m .nil = m.nilM := Con.nil_iota' ..
  def Con.ext_iota : Con.recL m (.ext Γ A) = m.extM Γ (Con.recL m Γ) A (Ty.recL m A) := Con.ext_iota' ..

  def Ty.U_iota : Ty.recL m .U = m.UM Γ (Con.recL m Γ) := Ty.U_iota' ..
  def Ty.Pi_iota : Ty.recL m (.Pi A B) = m.PiM Γ (Con.recL m Γ) A (Ty.recL m A) B (Ty.recL m B) := Ty.Pi_iota' ..

  attribute [irreducible] Con.recL
  attribute [irreducible] Ty.recL
  attribute [irreducible] Tm.recL
  attribute [irreducible] Var.recL
end Iota
