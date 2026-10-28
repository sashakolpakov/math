import OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorIrrelevantTorsion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IntegerCoordinateBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Saturation

/-! # Base Change Bound -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.BaseChangeBound.GradedHilbert

noncomputable section

/-!
A flat projective quotient over a noetherian ring has one saturation
bound valid after every coefficient-ring base change.
-/

open _root_.MvPolynomial TensorProduct _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorIrrelevantTorsion.ProjectiveCech

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}

theorem projectiveQuotient_uniform_saturation_baseChange
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) [Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))] :
    ∃ N : ℕ, ∀ (S : Type u) [CommRing S] [Algebra R S], ∀ d ≥ N,
      Hilbert.Polynomial.GradedHilbert.degreeRelations (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)).toIdeal d =
        Hilbert.Polynomial.GradedHilbert.degreeRelations (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal d := by
  obtain ⟨N, hN⟩ := TensorIrrelevantTorsion.ProjectiveCech.eventual_tensor_no_irrelevant_torsion (σ := Fin (n + 1))
    R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.coordinateChartDegreeZero_flat I)
  refine ⟨N, fun S _ _ d hd => ?_⟩
  let J := Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I
  apply le_antisymm
  · intro f hf
    let q : Graded.Quotient.GradedHilbert.quotientGrading J d := ⟨Ideal.Quotient.mk J.toIdeal f.val, f.val, f.property, rfl⟩
    let E := IntegerCoordinateBaseChange.GradedHilbert.integerQuotientGradingBaseChangeEquiv (S := S) I d
    let x := E.symm q
    have hx : x = 0 := by
      apply hN (d : ℤ) (by exact_mod_cast hd) S x
      intro i
      obtain ⟨k, hk⟩ := (Projective.Saturation.GradedHilbert.mem_projectiveSaturation_iff J f.property).mp hf i
      refine ⟨k, ?_⟩
      apply (Graded.BaseChange.GradedHilbert.quotientBaseChangeEquiv (S := S) I).injective
      rw [map_zero, IntegerCoordinateBaseChange.GradedHilbert.quotientBaseChangeEquiv_scalar,
        ← IntegerCoordinateBaseChange.GradedHilbert.integerQuotientGradingBaseChangeEquiv_val]
      change Ideal.Quotient.mk J.toIdeal (MvPolynomial.map (algebraMap R S) (X i ^ k)) *
        (E (E.symm q)).val = 0
      rw [LinearEquiv.apply_symm_apply, map_pow, MvPolynomial.map_X]
      change Ideal.Quotient.mk J.toIdeal (X i ^ k) * Ideal.Quotient.mk J.toIdeal f.val = 0
      rw [← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hk
    have hq : q = 0 := by
      have he := congrArg E hx
      simpa only [x, LinearEquiv.apply_symm_apply, map_zero] using he
    exact Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val hq)
  · intro f hf
    exact (Projective.Saturation.GradedHilbert.le_projectiveSaturation J) hf

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.BaseChangeBound.GradedHilbert
