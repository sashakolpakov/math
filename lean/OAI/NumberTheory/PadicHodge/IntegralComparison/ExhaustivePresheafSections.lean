import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.Order.Directed

/-! # Exhaustive Presheaf Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustivePresheafSections

noncomputable section

/-!
# IntegralComparison: presheaf sections over an increasing exhaustive family of full subcategories
-/

open _root_.CategoryTheory Opposite

universe u v w z

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
  (P : ℕ → ObjectProperty C) (hP : Monotone P) (hC : ∀ U, ∃ n, P n U)
  (M : D) (F : Cᵒᵖ ⥤ D)

abbrev Stage (n : ℕ) := (Functor.const (P n).FullSubcategoryᵒᵖ).obj M ⟶ (P n).ι.op ⋙ F

def restrict (n m : ℕ) (hnm : n ≤ m) (a : Stage P M F m) : Stage P M F n :=
  Functor.whiskerLeft (ObjectProperty.ιOfLE (hP hnm)).op a

def restrictGlobal (a : (Functor.const Cᵒᵖ).obj M ⟶ F) (n : ℕ) : Stage P M F n :=
  Functor.whiskerLeft (P n).ι.op a

def Compatible (a : ∀ n, Stage P M F n) : Prop :=
  ∀ n m (hnm : n ≤ m), restrict P hP M F n m hnm (a m) = a n

theorem restrictGlobal_compatible (a : (Functor.const Cᵒᵖ).obj M ⟶ F) :
    Compatible P hP M F (restrictGlobal P M F a) := by
  intro n m hnm
  apply NatTrans.ext
  funext U
  rfl

def level (U : C) : ℕ := (hC U).choose

theorem level_property (U : C) : P (level P hC U) U := (hC U).choose_spec

def value (a : ∀ n, Stage P M F n) (U : C) : M ⟶ F.obj (op U) :=
  (a (level P hC U)).app (op ⟨U, level_property P hC U⟩)

theorem value_eq (a : ∀ n, Stage P M F n) (ha : Compatible P hP M F a)
    (U : C) (n : ℕ) (hn : P n U) : value P hC M F a U = (a n).app (op ⟨U, hn⟩) := by
  let l := level P hC U
  let m := max l n
  have h₁ := congrArg (fun t : Stage P M F l => t.app (op ⟨U, level_property P hC U⟩))
    (ha l m (le_max_left l n))
  have h₂ := congrArg (fun t : Stage P M F n => t.app (op ⟨U, hn⟩))
    (ha n m (le_max_right l n))
  exact h₁.symm.trans h₂

def assemble (a : ∀ n, Stage P M F n) (ha : Compatible P hP M F a) : (Functor.const Cᵒᵖ).obj M ⟶ F where
  app U := value P hC M F a U.unop
  naturality U V α := by
    let l := max (level P hC U.unop) (level P hC V.unop)
    have hU : P l U.unop := hP (le_max_left _ _) U.unop (level_property P hC U.unop)
    have hV : P l V.unop := hP (le_max_right _ _) V.unop (level_property P hC V.unop)
    have h := (a l).naturality (ObjectProperty.homMk α.unop :
      (⟨V.unop, hV⟩ : (P l).FullSubcategory) ⟶ ⟨U.unop, hU⟩).op
    exact (congrArg (fun t => 𝟙 M ≫ t) (value_eq P hP hC M F a ha V.unop l hV)).trans
      (h.trans (congrArg (fun t => t ≫ F.map α) (value_eq P hP hC M F a ha U.unop l hU)).symm)

theorem assemble_restrictGlobal (a : (Functor.const Cᵒᵖ).obj M ⟶ F) :
    assemble P hP hC M F (restrictGlobal P M F a) (restrictGlobal_compatible P hP M F a) = a := by
  apply NatTrans.ext
  funext U
  rfl

theorem restrictGlobal_assemble (a : ∀ n, Stage P M F n) (ha : Compatible P hP M F a) (n : ℕ) :
    restrictGlobal P M F (assemble P hP hC M F a ha) n = a n := by
  apply NatTrans.ext
  funext U
  exact value_eq P hP hC M F a ha U.unop.obj n U.unop.property

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustivePresheafSections
