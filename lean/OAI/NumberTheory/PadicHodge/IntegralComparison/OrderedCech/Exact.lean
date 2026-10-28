import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Retraction
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Exact -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Exact

noncomputable section

/-! Exactness passes through the proved native ordered Čech retraction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {D : Type v} [Category D] [Abelian D] [HasProducts.{u} D]
  {ι : Type u} [LinearOrder ι] (U : ι → C) (P : Cᵒᵖ ⥤ D)

theorem ordered (n : ℕ) (h : (Cech.TupleRestrictionFunctor.complex U P).ExactAt n) :
    (Projection.complex U P).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at h ⊢
  apply (IsZero.iff_id_eq_zero _).mpr
  let H := HomologicalComplex.homologyFunctor D (.up ℕ) n
  have he := congrArg H.map (Retraction.inclusion_map U P)
  rw [H.map_comp, H.map_id] at he
  apply he.symm.trans
  erw [h.eq_zero_of_tgt (H.map (Retraction.inclusion U P)), zero_comp]
  rfl

theorem augmented (n : ℕ)
    (h : (Cech.TupleRestrictionFunctor.complex U P).ExactAt (n + 1)) :
    (AugmentedOrdered.Cech.complex U P).ExactAt (n + 2) := by
  have h' := ordered U P (n + 1) h
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)] at h'
  rw [HomologicalComplex.exactAt_iff' _ (n + 1) (n + 2) (n + 3) (by simp) (by simp)]
  simpa [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    Projection.complex, AugmentedOrdered.Cech.complex,
    CochainComplex.of.d, Projection.object,
    Projection.differential] using h'

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Exact
