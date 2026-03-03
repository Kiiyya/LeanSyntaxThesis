import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Data.Multiset.FinsetOps
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.UnionInter

/-
  `{Γ}` < `{Γ, A}` < `{Γ, A, a}`

  Multiset characteristic: Take one elem, replace with any amount of elements which are strictly smaller that the orig:
  `{Γ, A}` < `{ (Γ; A) }` works because `Γ < ..`, and `A < ..`.
-/


/- # General about Multisets -/

variable {α : Type*} {a b c : α}

@[simp] theorem Multiset.not_empty_2 : ({a, b} : Multiset α) ≠ 0 := by aesop
@[simp] theorem Multiset.not_empty_3 : ({a, b, c} : Multiset α) ≠ 0 := by aesop
attribute [-simp] Multiset.insert_eq_cons
-- @[aesop unsafe 50% apply] def Multiset.cons_eq_insert (a : α) (s : Multiset α) : a ::ₘ s = insert a s := (insert_eq_cons a s).symm



/- # More specific to DM -/

variable [Preorder α]

namespace DershowitzManna.Notation
  scoped infix:50 " << " => Multiset.IsDershowitzMannaLT
end DershowitzManna.Notation
open DershowitzManna.Notation

instance : Trans
    (Multiset.IsDershowitzMannaLT (α := α))
    (Multiset.IsDershowitzMannaLT (α := α))
    (Multiset.IsDershowitzMannaLT (α := α))
  where
    trans := Multiset.IsDershowitzMannaLT.trans

@[aesop 90%] theorem DershowitzManna.proj_2_1 : {a} << {a, b} := ⟨{a}, {}, {b}, by aesop⟩
@[aesop 90%] theorem DershowitzManna.proj_1_3 : {a} << {a, b, c} := ⟨{a}, {}, {b, c}, by aesop⟩
@[aesop 90%] theorem DershowitzManna.proj_2_3 : {a, b} << {a, b, c} := ⟨{a, b}, {}, {c}, by aesop⟩
/-- DershowitzManna characteristic: Take one elem, replace with any amount of elements which are strictly smaller that the original:
  `{Γ, A}` < `{ (Γ; A) }` works because `Γ < ..`, and `A < ..`.  -/
@[aesop 75%] theorem DershowitzManna.lift_lt (hb : b < a) : {b} << {a} :=
  ⟨{}, {b}, {a}, by aesop, by aesop, by aesop,
    fun y h => match h with
      | .head _ => by aesop
      | .tail _ h => nomatch h⟩
@[aesop 75%] theorem DershowitzManna.lift_lt_2 (hb : b < a) (hc : c < a) : {b, c} << {a} :=
  ⟨{}, {b, c}, {a}, by aesop, by aesop, by aesop,
    fun y h => match h with
      | .head _ => by aesop
      | .tail _ (.head _) => by aesop
      | .tail _ (.tail _ h) => nomatch h⟩

/- Main proof idea: You can just add whatever to the common multiset. -/
@[aesop 10%] theorem DershowitzManna.shave1 (M N : Multiset α) (h : M << N) : {a} + M << {a} + N :=
  let ⟨Q, W, E, h⟩ := h
  ⟨
  {a} + Q,
  W,
  E,
  by aesop
⟩

@[aesop 10%] theorem DershowitzManna.shave (M : Multiset α) {A B} (h : A << B) : M + A << M + B := by
  use M
  use A
  use B
  exact ⟨
    sorry,
    rfl,
    rfl,
    fun a ha => sorry
  ⟩
