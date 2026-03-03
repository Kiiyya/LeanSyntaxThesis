import Aesop
import Qq
import Lean
import Syntax.Erased
import Syntax.Wellformed
import Syntax.AllTogether
import Mathlib.Data.Quot

set_option linter.unusedVariables false

/-
  # Quotienting

  Tm Γ "id A" = Tm Γ "A"
  "id x" : Tm Γ A
  "id x" ≠ "x"
  ⟦"id x"⟧ = ⟦"x"⟧

-/


instance Con.setoid : Setoid Con := ⟨ConConv, ⟨fun Γ => ConWConv.refl Γ, ConWConv.symm, ConWConv.trans⟩⟩
instance Ty.setoid : Setoid (Ty Γ) := ⟨TyConv, sorry⟩
instance Tm.setoid : Setoid (Tm Γ A) := ⟨TmConv, sorry⟩
instance Var.setoid : Setoid (Var Γ A) := ⟨sorry, sorry⟩
instance Subst.setoid : Setoid (Subst Γ Δ) := ⟨sorry, sorry⟩

def ConC : Type := @Quotient (α := Con) Con.setoid
def TyC (Γ : ConC) : Type := Quotient.liftOn Γ (fun Γ => @Quotient (Ty Γ) Ty.setoid) (fun Γ Δ c => by
    dsimp
    have : Ty Γ = Ty Δ := Ty.cast c
    have : @Quotient (Ty Γ) (@Ty.setoid Γ) = @Quotient (Ty Δ) (@Ty.setoid Δ) := by sorry
    exact this
  )
def TmC (Γ : ConC) (A : TyC Γ) : Type := Quotient.rec (fun Γ => Quotient.rec (fun A => @Quotient (Tm Γ A) Tm.setoid) sorry) sorry Γ A
def SubstC (Γ Δ : ConC) : Type := Quotient.rec (fun Γ => Quotient.rec (fun Δ => @Quotient (Subst Γ Δ) Subst.setoid) sorry) sorry Γ Δ
def VarC (Γ : ConC) (A : TyC Γ) : Type := Quotient.rec (fun Γ => Quotient.rec (fun A => @Quotient (Var Γ A) Var.setoid) sorry) sorry Γ A

def ConC.nil : ConC := ⟦Con.nil⟧
def ConC.ext (Γq : ConC) (Aq : TyC Γq) : ConC :=
  Quotient.rec
    (fun (Γ : Con) (Aq : TyC ⟦Γ⟧) => Quotient.rec
      (fun (A : Ty Γ) =>
        ⟦Con.ext Γ A⟧
      )
      sorry
      Aq
    )
    sorry
    Γq Aq


def TyC.U : TyC Γ := Quotient.recOn Γ (fun Γ => ⟦@Ty.U Γ⟧) sorry
def TyC.El (t : TmC Γ .U) : TyC Γ := Quotient.recOn Γ (fun Γ => Quotient.rec (fun t => ⟦.El t⟧) sorry) sorry t
def TyC.Pi (A : TyC Γ) (B : TyC (.ext Γ A)) : TyC Γ :=
  Quotient.rec (motive := fun (Γ : ConC) => (A : TyC Γ) -> (B : TyC (ConC.ext Γ A)) -> TyC Γ)
    (fun (Γ:Con) (A : TyC ⟦Γ⟧) (B : TyC (ConC.ext ⟦Γ⟧ A)) =>
      Quotient.rec --(motive := fun (A : TyC ⟦Γ⟧) => (B : TyC (ConC.ext ⟦Γ⟧ A)) -> TyC ⟦Γ⟧)
        (fun (A : Ty Γ) (B : TyC (ConC.ext ⟦Γ⟧ ⟦A⟧)) =>
          Quotient.rec
            (fun B => ⟦.Pi A B⟧)
            sorry
            B
        )
        sorry
        A B
    )
    sorry
    Γ A B

def TyC.subst {Γ Δ : ConC} (A : TyC Δ) (σ : SubstC Γ Δ) : TyC Γ :=
  Quotient.rec (motive := fun Γ => (Δ : ConC) -> (A : TyC Δ) -> (σ : SubstC Γ Δ) -> TyC Γ)
    (fun Γ Δ A σ =>
      Quotient.rec (motive := fun Δ => (A : TyC Δ) -> (σ : SubstC ⟦Γ⟧ Δ) -> TyC ⟦Γ⟧)
        (fun Δ A σ =>
          Quotient.rec (motive := fun A => (σ : SubstC ⟦Γ⟧ ⟦Δ⟧) -> TyC ⟦Γ⟧)
            (fun A σ =>
              Quotient.rec (motive := fun σ => TyC ⟦Γ⟧)
                (fun σ => ⟦A.subst σ⟧)
                sorry
                σ
            )
            sorry
            A σ
        )
        sorry
        Δ A σ
    )
    sorry
    Γ Δ A σ

def TmC.subst {Γ Δ : ConC} {A : TyC Δ} (t : TmC Δ A) (σ : SubstC Γ Δ) : TmC Γ (TyC.subst A σ) :=
  Quotient.rec (motive := fun (Γ : ConC) => (Δ : ConC) -> (A : TyC Δ) -> (t : TmC Δ A) -> (σ : SubstC Γ Δ) -> TmC Γ (TyC.subst A σ))
    (fun (Γ : Con) Δ A t σ =>
      Quotient.rec (motive := fun (Δ : ConC) => (A : TyC Δ) -> (t : TmC Δ A) -> (σ : SubstC ⟦Γ⟧ Δ) -> TmC ⟦Γ⟧ (TyC.subst A σ))
        (fun (Δ : Con) A t σ =>
          Quotient.rec (motive := fun (A : TyC ⟦Δ⟧) => (t : TmC ⟦Δ⟧ A) -> (σ : SubstC ⟦Γ⟧ ⟦Δ⟧) -> TmC ⟦Γ⟧ (TyC.subst A σ))
            (fun (A : Ty Δ) t σ =>
              Quotient.rec --(motive := fun (t : TmC ⟦Δ⟧ ⟦A⟧) => (σ : SubstC ⟦Γ⟧ ⟦Δ⟧) -> TmC ⟦Γ⟧ (@substTyQ ⟦Γ⟧ ⟦Δ⟧ ⟦A⟧ σ))
                (fun (t : Tm Δ A) σ =>
                  Quotient.rec --(motive := fun (σ : SubstC ⟦Γ⟧ ⟦Δ⟧) => TmC ⟦Γ⟧ (@substTyQ ⟦Γ⟧ ⟦Δ⟧ ⟦A⟧ σ))
                    (fun (σ : Subst Γ Δ) => ⟦@Tm.subst Γ Δ A t σ⟧) -- lmao
                    sorry
                    σ
                )
                sorry
                t σ
            )
            sorry
            A t σ
        )
        sorry
        Δ A t σ
    )
    sorry
    Γ Δ A t σ

def SubstC.comp {Γ Θ Δ : ConC} (δ : SubstC Θ Δ) (σ : SubstC Γ Θ) : SubstC Γ Δ :=
  Quotient.rec                     (motive := fun (Γ : ConC) => (Θ : ConC) -> (Δ : ConC) -> (δ : SubstC  Θ  Δ) -> (σ : SubstC  Γ   Θ ) -> SubstC  Γ   Δ )
    (fun Γ Θ Δ δ σ => Quotient.rec (motive := fun (Θ : ConC) =>               (Δ : ConC) -> (δ : SubstC  Θ  Δ) -> (σ : SubstC ⟦Γ⟧  Θ ) -> SubstC ⟦Γ⟧  Δ )
      (fun Θ Δ δ σ => Quotient.rec (motive := fun (Δ : ConC) =>                             (δ : SubstC ⟦Θ⟧ Δ) -> (σ : SubstC ⟦Γ⟧ ⟦Θ⟧) -> SubstC ⟦Γ⟧  Δ )
        (fun Δ δ σ => Quotient.rec (motive := fun (δ : SubstC ⟦Θ⟧ ⟦Δ⟧) =>                                         (σ : SubstC ⟦Γ⟧ ⟦Θ⟧) -> SubstC ⟦Γ⟧ ⟦Δ⟧)
          (fun δ σ => Quotient.rec (motive := fun (σ : SubstC ⟦Γ⟧ ⟦Θ⟧) =>                                                                 SubstC ⟦Γ⟧ ⟦Δ⟧)
            (fun (σ : Subst Γ Θ) =>
              ⟦@Subst.comp Γ Θ Δ δ σ⟧
            )
            sorry
            σ
          )
          sorry
          δ σ
        )
        sorry
        Δ δ σ
      )
      sorry
      Θ Δ δ σ
    )
    sorry
    Γ Θ Δ δ σ


def SubstC.nil : SubstC Γ .nil :=
  Quotient.rec (fun Γ => ⟦.nil⟧) sorry Γ

def SubstC.cons (δ : SubstC Γ Δ) (t : TmC Γ (@TyC.subst Γ Δ A δ)) : SubstC Γ (Δ.ext A) :=
  Quotient.rec                     (motive := fun (Γ : ConC) => (Δ : ConC) -> (A : TyC Δ) -> (δ : SubstC  Γ   Δ ) -> (t : TmC  Γ  (TyC.subst           A  δ)) -> SubstC  Γ  (ConC.ext  Δ   A ))
    (fun Γ Δ A δ t => Quotient.rec (motive := fun (Δ : ConC) =>               (A : TyC Δ) -> (δ : SubstC ⟦Γ⟧  Δ ) -> (t : TmC ⟦Γ⟧ (TyC.subst           A  δ)) -> SubstC ⟦Γ⟧ (ConC.ext  Δ   A ))
      (fun Δ A δ t => Quotient.rec (motive := fun (A : TyC ⟦Δ⟧) =>                           (δ : SubstC ⟦Γ⟧ ⟦Δ⟧) -> (t : TmC ⟦Γ⟧ (TyC.subst           A  δ)) -> SubstC ⟦Γ⟧ (ConC.ext ⟦Δ⟧  A ))
        (fun A δ t => Quotient.rec (motive := fun (δ : SubstC ⟦Γ⟧ ⟦Δ⟧) =>                                            (t : TmC ⟦Γ⟧ (@TyC.subst ⟦Γ⟧ ⟦Δ⟧ ⟦A⟧ δ)) -> SubstC ⟦Γ⟧ (ConC.ext ⟦Δ⟧ ⟦A⟧))
          (fun δ t => Quotient.rec (motive := fun (t : TmC ⟦Γ⟧ (@TyC.subst ⟦Γ⟧ ⟦Δ⟧ ⟦A⟧ ⟦δ⟧)) =>                                                                  SubstC ⟦Γ⟧ (ConC.ext ⟦Δ⟧ ⟦A⟧))
            (fun t => ⟦Subst.cons δ t⟧)
            (by sorry)
            t
          )
          sorry
          δ t
        )
        sorry
        A δ t
      )
      sorry
      Δ A δ t
    )
    sorry
    Γ Δ A δ t


def SubstC.id : SubstC Γ Γ :=
  Quotient.rec (fun Γ => ⟦.id⟧) sorry Γ

def SubstC.wk (δ : SubstC Γ Δ) : SubstC (.ext Γ A) Δ :=
  Quotient.rec                   (motive := fun (Γ : ConC) => (Δ : ConC) -> (A : TyC  Γ ) -> (δ : SubstC  Γ   Δ ) -> SubstC (ConC.ext  Γ   A )  Δ )
    (fun Γ Δ A δ => Quotient.rec (motive := fun (Δ : ConC) =>               (A : TyC ⟦Γ⟧) -> (δ : SubstC ⟦Γ⟧  Δ ) -> SubstC (ConC.ext ⟦Γ⟧  A )  Δ )
      (fun Δ A δ => Quotient.rec (motive := fun (A : TyC ⟦Γ⟧) =>                             (δ : SubstC ⟦Γ⟧ ⟦Δ⟧) -> SubstC (ConC.ext ⟦Γ⟧  A ) ⟦Δ⟧)
        (fun A δ => Quotient.rec (motive := fun (δ : SubstC ⟦Γ⟧ ⟦Δ⟧) =>                                              SubstC (ConC.ext ⟦Γ⟧ ⟦A⟧) ⟦Δ⟧)
          (fun δ => ⟦Subst.wk δ⟧)
          sorry
          δ
        )
        sorry
        A δ
      )
      sorry
      Δ A δ
    )
    sorry
    Γ Δ A δ

def SubstC.wki : SubstC (.ext Γ W) Γ :=
  Quotient.rec (motive := fun Γ => (W : TyC Γ) -> SubstC (ConC.ext Γ W) Γ)
    (fun Γ W => Quotient.rec
      (fun W => ⟦@Subst.wki Γ W⟧)
      sorry
      W
    )
    sorry
    Γ W

def SubstC.lift {Γ Δ} {A : TyC Δ} (σ : SubstC Γ Δ) : SubstC (Γ.ext (TyC.subst A σ)) (Δ.ext A) :=
  Quotient.rec                   (motive := fun (Γ : ConC) => (Δ : ConC) -> (A : TyC  Δ ) -> (σ : SubstC  Γ   Δ ) -> SubstC (ConC.ext  Γ  (@TyC.subst  Γ   Δ   A  σ)) (ConC.ext  Δ   A ))
    (fun Γ Δ A σ => Quotient.rec (motive := fun (Δ : ConC) =>               (A : TyC  Δ ) -> (σ : SubstC ⟦Γ⟧  Δ ) -> SubstC (ConC.ext ⟦Γ⟧ (@TyC.subst ⟦Γ⟧  Δ   A  σ)) (ConC.ext  Δ   A ))
      (fun Δ A σ => Quotient.rec (motive := fun (A : TyC ⟦Δ⟧) =>                             (σ : SubstC ⟦Γ⟧ ⟦Δ⟧) -> SubstC (ConC.ext ⟦Γ⟧ (@TyC.subst ⟦Γ⟧ ⟦Δ⟧  A  σ)) (ConC.ext ⟦Δ⟧  A ))
        (fun A σ => Quotient.rec (motive := fun (σ : SubstC ⟦Γ⟧ ⟦Δ⟧) =>                                              SubstC (ConC.ext ⟦Γ⟧ (@TyC.subst ⟦Γ⟧ ⟦Δ⟧ ⟦A⟧ σ)) (ConC.ext ⟦Δ⟧ ⟦A⟧))
          (fun σ => ⟦@Subst.lift Γ Δ A σ⟧)
          sorry
          σ
        )
        sorry
        A σ
      )
      sorry
      Δ A σ
    )
    sorry
    Γ Δ A σ

-- def SubstC.wki : SubstC (.ext Γ B) Γ := wk id
@[simp] def TyC.subst_id {A : TyC Γ} : TyC.subst A SubstC.id = A := by sorry

def SubstC.apply (a : TmC Γ A) : SubstC Γ (Γ.ext A) :=
  Quotient.rec                 (motive := fun Γ => (A : TyC Γ) -> TmC  Γ  A -> SubstC  Γ  (ConC.ext  Γ   A ))
    (fun Γ A a => Quotient.rec (motive := fun A =>                TmC ⟦Γ⟧ A -> SubstC ⟦Γ⟧ (ConC.ext ⟦Γ⟧  A ))
      (fun A a => Quotient.rec (motive := fun a =>                             SubstC ⟦Γ⟧ (ConC.ext ⟦Γ⟧ ⟦A⟧))
        (fun a => ⟦@Subst.apply Γ A a⟧)
        sorry
        a
      )
      sorry
      A a
    )
    sorry
    Γ A a

/-- `vz {Γ} {A : Ty Γ} : Var (Γ, A) A[wki]`. -/
def VarC.vz : VarC (.ext Γ A) (TyC.subst A .wki) :=
  Quotient.rec (fun Γ => Quotient.rec (fun A => ⟦.vz⟧) sorry) sorry Γ A

/-- `vs {Γ} {A : Ty Γ} {B : Ty Γ} : Var Γ A -> Var (Γ, B) A[wki]`. -/
def VarC.vs (v : VarC Γ A) : VarC (.ext Γ B) (TyC.subst A .wki) :=
  Quotient.rec (motive := fun Γ => (A : TyC Γ) -> (B : TyC Γ) -> (v : VarC Γ A) -> VarC (ConC.ext Γ B) (TyC.subst A .wki)) (fun Γ : Con =>
    Quotient.rec (fun A : Ty Γ =>
      Quotient.rec (fun B : Ty Γ =>
        Quotient.rec (fun (v : Var Γ A) =>
          ⟦@Var.vs Γ A B v⟧
        ) sorry
      ) sorry
    ) sorry
  ) sorry
  Γ A B v

def TmC.var {Γ} {A : TyC Γ} (v : VarC Γ A) : TmC Γ A :=
  Quotient.rec (motive := fun Γ => (A : TyC Γ) -> (v : VarC Γ A) -> TmC Γ A) (fun Γ =>
    Quotient.rec (fun A =>
      Quotient.rec (fun v =>
        ⟦.var v⟧
      ) sorry
    ) sorry
  ) sorry
  Γ A v

-- example (a : Tm Γ A) : @SubstC.apply ⟦Γ⟧ ⟦A⟧ ⟦a⟧ = ⟦@Subst.apply Γ A a⟧ := rfl

def TmC.app {A : TyC Γ} {B : TyC (Γ.ext A)} (f : TmC Γ (.Pi A B)) (a : TmC Γ A) : TmC Γ (TyC.subst B (.apply a)) :=
  Quotient.rec                     (motive := fun (Γ : ConC) => (A : TyC  Γ ) -> (B : TyC (ConC.ext  Γ  A)) -> (f : TmC  Γ  (.Pi  A  B)) -> (a : TmC  Γ   A ) -> TmC  Γ  (@TyC.subst Γ (.ext Γ A) B  (.apply a)))
    (fun Γ A B f a => Quotient.rec (motive := fun (A : TyC ⟦Γ⟧) =>               (B : TyC (ConC.ext ⟦Γ⟧ A)) -> (f : TmC ⟦Γ⟧ (.Pi  A  B)) -> (a : TmC ⟦Γ⟧  A ) -> TmC ⟦Γ⟧ (@TyC.subst ⟦Γ⟧ (.ext ⟦Γ⟧ A)  B  (.apply a)))
      (fun A B f a => Quotient.rec (motive := fun (B : TyC (ConC.ext ⟦Γ⟧ ⟦A⟧)) =>                              (f : TmC ⟦Γ⟧ (.Pi ⟦A⟧ B)) -> (a : TmC ⟦Γ⟧ ⟦A⟧) -> TmC ⟦Γ⟧ (@TyC.subst ⟦Γ⟧ (.ext ⟦Γ⟧ ⟦A⟧)  B  (.apply a)))
        (fun B f a => Quotient.rec (motive := fun (f : TmC ⟦Γ⟧ (TyC.Pi ⟦A⟧ ⟦B⟧)) =>                                                         (a : TmC ⟦Γ⟧ ⟦A⟧) -> TmC ⟦Γ⟧ (@TyC.subst ⟦Γ⟧ (.ext ⟦Γ⟧ ⟦A⟧) ⟦B⟧ (.apply a)))
          (fun f a => Quotient.rec (motive := fun (a : TmC ⟦Γ⟧ ⟦A⟧) =>                                                                                           TmC ⟦Γ⟧ (@TyC.subst ⟦Γ⟧ (.ext ⟦Γ⟧ ⟦A⟧) ⟦B⟧ (.apply a)))
            (fun a => ⟦@Tm.app Γ A B f a⟧)
            sorry
            a
          )
          sorry
          f a
        )
        sorry
        B f a
      )
      sorry
      A B f a
    )
    sorry
    Γ A B f a

def TmC.lam {Γ} {A : TyC Γ} {B : TyC (.ext Γ A)} (body : TmC (.ext Γ A) B) : TmC Γ (.Pi A B) :=
  Quotient.rec                      (motive := fun (Γ : ConC) => (A : TyC  Γ ) -> (B : TyC (ConC.ext  Γ  A)) -> (body : TmC (ConC.ext  Γ   A ) B) -> TmC  Γ  (@TyC.Pi  Γ   A   B ))
    (fun Γ A B body => Quotient.rec (motive := fun (A : TyC ⟦Γ⟧) =>               (B : TyC (ConC.ext ⟦Γ⟧ A)) -> (body : TmC (ConC.ext ⟦Γ⟧  A ) B) -> TmC ⟦Γ⟧ (@TyC.Pi ⟦Γ⟧  A   B ))
      (fun A B body => Quotient.rec (motive := fun (B : TyC (ConC.ext ⟦Γ⟧ ⟦A⟧)) =>                              (body : TmC (ConC.ext ⟦Γ⟧ ⟦A⟧) B) -> TmC ⟦Γ⟧ (@TyC.Pi ⟦Γ⟧ ⟦A⟧  B ))
        (fun B body => Quotient.rec (motive := fun (body : TmC (ConC.ext ⟦Γ⟧ ⟦A⟧) ⟦B⟧) =>                                                            TmC ⟦Γ⟧ (@TyC.Pi ⟦Γ⟧ ⟦A⟧ ⟦B⟧))
          (fun body => ⟦@Tm.lam Γ A B body⟧)
          sorry
          body
        )
        sorry
        B body
      )
      sorry
      A B body
    )
    sorry
    Γ A B body
