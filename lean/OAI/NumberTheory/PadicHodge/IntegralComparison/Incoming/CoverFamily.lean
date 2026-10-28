import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionRestriction
import Mathlib.CategoryTheory.Sites.Sheaf

/-! # Cover Family -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.CoverFamily.Family

noncomputable section

/-!
# IntegralComparison: compatible sections on full subsites give matching families on their covering sieves
-/

open _root_.CategoryTheory Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionRestriction

universe u v w z

variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (M : ModuleCat.{w} R) {ι : Type z} (P : ι → ObjectProperty C)
  (hP : ∀ i {U V : C}, (U ⟶ V) → P i V → P i U)

def sieve (T : C) : Sieve T where
  arrows U _ := ∃ i, P i U
  downward_closed := by
    intro U V α h β
    obtain ⟨i, hi⟩ := h
    exact ⟨i, hP i β hi⟩

variable (F : Cᵒᵖ ⥤ ModuleCat.{w} R) (a : ∀ i, SectionRestriction.Sections R M (P i) F)

def Compatible : Prop := ∀ i j (T : C) (hi : P i T) (hj : P j T),
  (a i).app (op ⟨T, hi⟩) = (a j).app (op ⟨T, hj⟩)

def value (T : C) (hT : ∃ i, P i T) : M ⟶ F.obj (op T) :=
  (a hT.choose).app (op ⟨T, hT.choose_spec⟩)

variable (ha : Family.Compatible R M P F a)

include ha in
theorem value_eq (T : C) (hT : ∃ i, P i T) (i : ι) (hi : P i T) :
    value R M P F a T hT = (a i).app (op ⟨T, hi⟩) :=
  ha hT.choose i T hT.choose_spec hi

include ha hP in
theorem value_natural {U T : C} (α : U ⟶ T) (hT : ∃ i, P i T) (hU : ∃ i, P i U) :
    value R M P F a T hT ≫ F.map α.op = value R M P F a U hU := by
  obtain ⟨i, hi⟩ := hT
  have hUi := hP i α hi
  rw [value_eq R M P F a ha T _ i hi, value_eq R M P F a ha U _ i hUi]
  have h := (a i).naturality (ObjectProperty.homMk α :
    (⟨U, hUi⟩ : (P i).FullSubcategory) ⟶ ⟨T, hi⟩).op
  exact h.symm.trans (Category.id_comp _)

def family (T : C) : Presieve.FamilyOfElements (F ⋙ coyoneda.obj (op M)) (sieve P hP T).arrows :=
  fun U _ hU => value R M P F a U hU

include ha in
theorem family_compatible (T : C) : (family R M P hP F a T).Compatible := by
  apply (Presieve.compatible_iff_sieveCompatible _).mpr
  intro U W α β hα
  exact (value_natural R M P hP F a ha β hα ((sieve P hP T).downward_closed hα β)).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.CoverFamily.Family
