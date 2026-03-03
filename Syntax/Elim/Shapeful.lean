import Aesop
import Qq
import Lean
import Syntax.Erased
import Syntax.Wellformed
import Syntax.AllTogether
import Syntax.Elim.Cases

set_option pp.fieldNotation.generalized false
set_option linter.unusedVariables false
set_option pp.proofs true


structure Disp where
  ConD : Con -> Sort u
  TyD : (Γ : Con) -> (Γd : ConD Γ) -> (A : Ty Γ) -> Sort u
  TmD : (Γ : Con) -> (Γd : ConD Γ) -> (A : Ty Γ) -> TyD Γ Γd A -> Tm Γ A -> Sort u
  VarD : (Γ : Con) -> (Γd : ConD Γ) -> (A : Ty Γ) -> TyD Γ Γd A -> Var Γ A -> Sort u
  SubstD : (Γ : Con) -> (Γd : ConD Γ) -> (Δ : Con) -> (Δd : ConD Δ) -> Subst Γ Δ -> Sort u
  TmD_conv : {Γ : Con} -> {Γd : ConD Γ} -> {X Y : Ty Γ} -> {Xd : TyD Γ Γd X} -> {Yd : TyD Γ Γd Y} ->
    {t : Tm Γ X} -> (Xc : TyConv X Y) -> TmD Γ Γd X Xd t = TmD Γ Γd Y Yd (t.conv Xc)
  nilD : ConD .nil
  extD : (Γ : Con) -> (Γd : ConD Γ) -> (A : Ty Γ) -> (Ad : TyD Γ Γd A) -> ConD (.ext Γ A)
  UD : (Γ : Con) -> (Γd : ConD Γ) -> TyD Γ Γd .U
  PiD :
    (Γ : Con) -> (Γd : ConD Γ) ->
    (A : Ty Γ) -> (Ad : TyD Γ Γd A) ->
    (B : Ty (Γ.ext A)) -> (Bd : TyD (.ext Γ A) (extD Γ Γd A Ad) B) ->
    TyD Γ Γd (.Pi A B)
  ElD :
    (Γ : Con) -> (Γd : ConD Γ) ->
    (t : Tm Γ .U) -> (td : TmD Γ Γd .U (UD Γ Γd) t) ->
    TyD Γ Γd (.El t)
  varD : (Γ : Con) -> (Γd : ConD Γ) -> (A : Ty Γ) -> (Ad : TyD Γ Γd A) -> (v : Var Γ A) -> (vd : VarD Γ Γd A Ad v) -> TmD Γ Γd A Ad (.var v)
  appD :
    {Γ : Con} -> (Γd : ConD Γ) ->
    {A : Ty Γ} -> (Ad : TyD Γ Γd A) ->
    {B : Ty (Γ.ext A)} -> (Bd : TyD (.ext Γ A) (extD Γ Γd A Ad) B) ->
    (f : Tm Γ (.Pi A B)) -> (fd : TmD Γ Γd (.Pi A B) (PiD Γ Γd A Ad B Bd) f) ->
    (a : Tm Γ A) -> (ad : TmD Γ Γd A Ad a) ->
    TmD Γ Γd
      (Ty.subst B (.apply a))
      sorry -- ? = `Ty.rec B[a] : TyD ...`
      (.app f a)
  lamD :
    (Γ : Con) -> (Γd : ConD Γ) ->
    (A : Ty Γ) -> (Ad : TyD Γ Γd A) ->
    (B : Ty (Γ.ext A)) -> (Bd : TyD (.ext Γ A) (extD Γ Γd A Ad) B) ->
    (body : Tm (.ext Γ A) B) -> (bodyd : TmD (.ext Γ A) (extD Γ Γd A Ad) B Bd body) ->
    TmD Γ Γd (.Pi A B) (PiD Γ Γd A Ad B Bd) (.lam body)
  piD :
    (Γ : Con) -> (Γd : ConD Γ) ->
    (A : Tm Γ .U) -> (Ad : TmD Γ Γd .U (UD Γ Γd) A) ->
    (B : Tm (Γ.ext (.El A)) .U) -> (Bd : TmD (.ext Γ (.El A)) (extD Γ Γd (.El A) (ElD Γ Γd A Ad)) .U (UD _ _) B) ->
    TmD Γ Γd .U (UD _ _) (.pi A B)

mutual
  inductive ConRec (d : Disp) : (Γ : Con) -> d.ConD Γ -> Prop
  | nil : ConRec d .nil d.nilD
  | ext : ConRec d Γ Γd -> TyRec d Γ Γd A Ad -> ConRec d (.ext Γ A) (d.extD Γ Γd A Ad)

  inductive TyRec (d : Disp) : (Γ : Con) -> (Γd : d.ConD Γ) -> (A : Ty Γ) -> d.TyD Γ Γd A -> Prop
  | U : TyRec d Γ Γd .U (d.UD Γ Γd)
  | Pi : TyRec d Γ Γd A Ad -> TyRec d (.ext Γ A) (d.extD Γ Γd A Ad) B Bd -> TyRec d Γ Γd (.Pi A B) (d.PiD Γ Γd A Ad B Bd)
  | El : TyRec d Γ Γd (.El t) (d.ElD Γ Γd t td)

  -- but `TmRec` not necessary.
end

mutual
  -- def Con.rec (d : Disp) (Γ : Con) : d.ConD Γ
  unsafe def Con.rec' (d : Disp) (Γ : Con) : (Γd : d.ConD Γ) ×' ConRec d Γ Γd :=
    let ⟨γ, Γe, Γw⟩ := Γ
    match γ, Γe with
    | 0, .nil => ⟨d.nilD, .nil⟩
    | γ+1, .ext Γe Ae =>
      let Γ : Con := ⟨γ, Γe, Γw.ext_Γw⟩
      let A : Ty Γ := ⟨Ae, Γw.ext_Aw⟩
      let ⟨Γd, Γd_graph⟩ := Γ.rec' d
      let ⟨Ad, Ad_graph⟩ := A.rec' d Γ Γd Γd_graph
      ⟨d.extD Γ Γd A Ad, .ext Γd_graph Ad_graph⟩

  -- Does it have to be a specific `Γd`? If yes, we need the restriction from `Γg`, if not, then... we don't.
  unsafe def Ty.rec' (d : Disp) (Γ : Con) (Γd : d.ConD Γ) (Γg : ConRec d Γ Γd) (X : Ty Γ)
    : (Xd : d.TyD Γ Γd X) ×' TyRec d Γ Γd X Xd
  :=
    let ⟨γ, Γe, Γw⟩ := Γ
    let ⟨Xe, Xw⟩ := X
    match h : Xe with
    | .U =>
      let Γ : Con := ⟨γ, Γe, Γw⟩
      ⟨d.UD Γ Γd, .U⟩
    | .Pi Ae Be =>
      let Γ := ⟨γ, Γe, Γw⟩
      let A := ⟨Ae, Xw.Pi_Aw⟩
      let B := ⟨Be, Xw.Pi_Bw⟩
      let ⟨Ad, Ag⟩ := Ty.rec' d Γ Γd Γg A
      let ⟨Bd, Bg⟩ := Ty.rec' d (.ext Γ A) (d.extD Γ Γd A Ad) (.ext Γg Ag) B
      ⟨d.PiD Γ Γd A Ad B Bd, .Pi Ag Bg⟩
    | .El te =>
      let Γ : Con := ⟨γ, Γe, Γw⟩
      let t : Tm Γ .U := ⟨te, Xw.El_tw⟩
      let td := Tm.rec' d Γ Γd Γg .U (d.UD Γ Γd) .U t
      ⟨d.ElD Γ Γd t td, sorry⟩
    | _ => sorry

  -- Tm.rec : ... -> TmD Γ (Con.rec Γ) ...
  unsafe def Tm.rec' (d : Disp)
    (Γ : Con) (Γd : d.ConD Γ) (Γg : ConRec d Γ Γd)
    (X : Ty Γ) (Xd : d.TyD Γ Γd X) (Xg : TyRec d Γ Γd X Xd)
    (t : Tm Γ X) : d.TmD Γ Γd X Xd t
  :=
    let ⟨γ, Γe, Γw⟩ := Γ
    let ⟨Xe, Xw⟩ := X
    let ⟨te, tw⟩ := t
    match te with
    | .var ve =>
      let Γ : Con := ⟨γ, Γe, Γw⟩
      let X : Ty Γ := ⟨Xe, Xw⟩
      let v : Var Γ X := ⟨ve, sorry⟩
      let vd := v.rec' d Γ Γd Γg X Xd Xg
      d.varD Γ Γd X Xd v vd
    | .lam Ae Be bodye =>
      let Γ : Con := ⟨γ, Γe, Γw⟩
      let X : Ty Γ := ⟨Xe, Xw⟩
      let A : Ty Γ := ⟨Ae, TmW.lam_wf₁ tw⟩
      let B : Ty (.ext Γ A) := ⟨Be, TmW.lam_wf₂ tw⟩
      let body : Tm (.ext Γ A) B := ⟨bodye, TmW.lam_wf₃ tw⟩
      let ⟨Ad, Ag⟩ := A.rec' d Γ Γd Γg
      let ⟨Bd, Bg⟩ := B.rec' d (.ext Γ A) (d.extD Γ Γd A Ad) (.ext Γg Ag)
      let bodyd := body.rec' d (.ext Γ A) (d.extD Γ Γd A Ad) (.ext Γg Ag) B Bd Bg
      have Xc : TyConv X (.Pi A B) := TmW.lam_inv tw
      let ret : d.TmD Γ Γd (.Pi A B) (d.PiD Γ Γd A Ad B Bd) (.lam body) := d.lamD Γ Γd A Ad B Bd body bodyd
      d.TmD_conv Xc ▸ ret
    | .app Ae Be fe ae =>
      let Γ : Con := ⟨γ, Γe, Γw⟩
      let X : Ty Γ := ⟨Xe, Xw⟩
      let A : Ty Γ := ⟨Ae, tw.app_wf₁⟩
      let B : Ty (.ext Γ A) := ⟨Be, tw.app_wf₂⟩
      let f : Tm Γ (.Pi A B) := ⟨fe, tw.app_wf₃⟩
      let a : Tm Γ A := ⟨ae, tw.app_wf₄⟩
      let ⟨Ad, Ag⟩ := A.rec' d Γ Γd Γg
      let ⟨Bd, Bg⟩ := B.rec' d (.ext Γ A) (d.extD Γ Γd A Ad) (.ext Γg Ag)
      let fd := f.rec' d Γ Γd Γg (.Pi A B) (d.PiD Γ Γd A Ad B Bd) (.Pi Ag Bg)
      let ad := a.rec' d Γ Γd Γg A Ad Ag
      have Xc : @TyConv Γ X (B.subst (.apply a)) := TmW.app_inv tw
      let BaD : d.TyD Γ Γd (B.subst (.apply a)) := sorry -- ! the problem
      let ret := d.appD Γd Ad Bd f fd a ad
      d.TmD_conv Xc ▸ ret
    | .pi Ae Be =>
      let Γ : Con := ⟨γ, Γe, Γw⟩
      let X : Ty Γ := ⟨Xe, Xw⟩
      let A : Tm Γ .U := ⟨Ae, tw.pi_wf₁⟩
      let B : Tm (.ext Γ (.El A)) .U := ⟨Be, tw.pi_wf₂⟩
      let Ad := Tm.rec' d Γ Γd Γg .U (d.UD _ _) .U A
      let Bd := Tm.rec' d (.ext Γ (.El A)) (d.extD Γ Γd (.El A) (d.ElD Γ Γd A Ad)) (.ext Γg .El) .U (d.UD _ _) .U B
      let ret := d.piD Γ Γd A Ad B Bd
      have Xc : @TyConv Γ X .U := tw.pi_inv
      d.TmD_conv Xc ▸ ret
    | _ => sorry

  unsafe def Var.rec' (d : Disp)
    (Γ : Con) (Γd : d.ConD Γ) (Γg : ConRec d Γ Γd)
    (X : Ty Γ) (Xd : d.TyD Γ Γd X) (Xg : TyRec d Γ Γd X Xd)
    (v : Var Γ X) : d.VarD Γ Γd X Xd v
  :=
    let ⟨γ+1, .ext Δe Be, Δw⟩ := Γ -- `Γ = (Δ; B)`
    let ⟨Xe, Xw⟩ := X -- `Δ; B ⊢ X`
    let ⟨ve, vw⟩ := v -- `Δ; B ⊢ v : X`
    match ve with
    | .vz =>
      let Δ : Con := ⟨γ, Δe, Δw.ext_Γw⟩
      let B : Ty Δ := ⟨Be, Δw.ext_Aw⟩
      let X : Ty (.ext Δ B) := ⟨Xe, Xw⟩
      have Xc : TyConv X (B.subst .wki) := sorry
      let ⟨Δd, Δg⟩ := Δ.rec' d
      let ⟨Bd, Bg⟩ := B.rec' d Δ Δd Δg
      sorry
    | .vs v => sorry
end

unsafe def Con.rec (d : Disp) (Γ : Con) : d.ConD Γ := Con.rec' d Γ |>.1

unsafe def Ty.rec (d : Disp) {Γ : Con} (A : Ty Γ) : d.TyD Γ (Con.rec d Γ) A
  := Ty.rec' d Γ (Con.rec' d Γ).1 (Con.rec' d Γ).2 A |>.1

-- -- set_option maxRecDepth 5000 in
-- unsafe def Tm.rec (d : Disp) {Γ : Con} {A : Ty Γ} (t : Tm Γ A)
--   : d.TmD Γ (Con.rec d Γ) A (Ty.rec d A) t
--   :=
--     let Γd := Con.rec' d Γ
--     let Ad := Ty.rec' d Γ Γd.1 Γd.2 A -- `maximum recursion depth has been reached` or whnf timeout
--     let res := Tm.rec' d Γ Γd.1 Γd.2 A Ad.1 Ad.2 t
--     res
