import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.SaturatedTensor
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IntegerCoordinateBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Saturation

/-! # Saturation Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.SaturationBaseChange.GradedHilbert

noncomputable section

/-! The uniform dimension-and-Hilbert-polynomial bound controls saturation after every coefficient-ring base change of a saturated flat projective family. -/

open _root_.MvPolynomial TensorProduct _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}

theorem uniform_saturated_saturation_baseChange
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hSat : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
    [Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))]
    (P : Polynomial ℚ) (hP : ∀ p : PrimeSpectrum R,
      Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
        (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I)).toIdeal P)
    (S : Type u) [CommRing S] [Algebra R S] (d : ℕ) (hd : RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n P ≤ d) :
      Hilbert.Polynomial.GradedHilbert.degreeRelations (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)).toIdeal d =
        Hilbert.Polynomial.GradedHilbert.degreeRelations (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal d := by
  let J := Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I
  apply le_antisymm
  · intro f hf
    let q : Graded.Quotient.GradedHilbert.quotientGrading J d := ⟨Ideal.Quotient.mk J.toIdeal f.val, f.val, f.property, rfl⟩
    let E := IntegerCoordinateBaseChange.GradedHilbert.integerQuotientGradingBaseChangeEquiv (S := S) I d
    let x := E.symm q
    have hx : x = 0 := by
      apply SaturatedTensor.GradedHilbert.uniform_saturated_tensor_no_irrelevant_torsion I hSat P hP d hd S x
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

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.SaturationBaseChange.GradedHilbert
