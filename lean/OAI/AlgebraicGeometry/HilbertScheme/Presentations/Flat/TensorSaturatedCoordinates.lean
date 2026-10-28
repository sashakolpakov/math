import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SaturatedCechAugmentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorFractionTorsion
import Mathlib.RingTheory.Flat.Basic

/-! # Tensor Saturated Coordinates -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.TensorSaturatedCoordinates.GradedHilbert

noncomputable section

/-! Tensoring saturated homogeneous coordinates with a flat coefficient
module preserves absence of irrelevant torsion, in every degree. -/

open _root_.MvPolynomial TensorProduct

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorFractionTorsion.GradedModules

universe u v
variable {R : Type u} [CommRing R] {n : ℕ}

theorem flat_saturated_tensor_no_irrelevant_torsion
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal) (d : ℕ)
    (A : Type v) [AddCommGroup A] [Module R A] [Module.Flat R A]
    (x : A ⊗[R] Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I (d : ℤ))
    (hx : ∀ i : Fin (n + 1), ∃ k : ℕ,
      ((TensorFractionTorsion.GradedModules.moduleScalarEnd (R := R) (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (X (R := R) i ^ k)).lTensor A)
        (((Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I (d : ℤ)).subtype.lTensor A) x) = 0) : x = 0 := by
  apply Module.Flat.lTensor_preserves_injective_linearMap
    (Cech.SectionMap.ProjectiveCech.moduleDegreeSectionMap (σ := Fin (n + 1)) R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ)) (SaturatedCechAugmentation.GradedHilbert.saturatedDegreeSectionMap_injective I hI d)
  rw [LinearMap.map_zero]
  apply (TensorProduct.piRight R R A (fun s : Finset (Fin (n + 1)) =>
    Graded.ModuleRestriction.ProjectiveCech.ModuleChart R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) s)).injective
  rw [LinearEquiv.map_zero]
  funext s
  rw [Cech.SectionMap.ProjectiveCech.moduleDegreeSectionMap_tensor_coordinate, Cech.SectionMap.ProjectiveCech.moduleDegreeSectionMap_proj]
  by_cases hs : s.card = 1
  · rw [ite_eq_left hs, LinearMap.lTensor_comp_apply]
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
    obtain ⟨k, hk⟩ := hx i
    exact TensorFractionTorsion.GradedModules.tensorFraction_zero_of_power_torsion (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (LaurentMonomials.ProjectiveCech.inversionMonomial R s)
      (X i) (LaurentMonomials.ProjectiveCech.inversionMonomial R (s.erase i)) (EventualDegreeFlatness.ProjectiveCech.inversionMonomial_factor_variable R s i hi) A _ k hk
  · rw [ite_eq_right hs, LinearMap.lTensor_zero, LinearMap.zero_apply]
    rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.TensorSaturatedCoordinates.GradedHilbert
