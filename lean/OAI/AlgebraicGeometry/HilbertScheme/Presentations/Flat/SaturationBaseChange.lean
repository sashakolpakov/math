import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.TensorSaturatedCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IntegerCoordinateBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Saturation

/-! # Saturation Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.SaturationBaseChange.GradedHilbert

noncomputable section

/-! Saturated homogeneous ideals remain saturated under arbitrary flat
coefficient-ring extensions, without noetherianity or degree bounds. -/

open _root_.MvPolynomial TensorProduct

universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A] {n : ℕ}

theorem flat_saturated_saturation_baseChange
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal) (d : ℕ) :
    Hilbert.Polynomial.GradedHilbert.degreeRelations (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)).toIdeal d =
      Hilbert.Polynomial.GradedHilbert.degreeRelations (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I).toIdeal d := by
  let J := Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I
  apply le_antisymm
  · intro f hf
    let q : Graded.Quotient.GradedHilbert.quotientGrading J d := ⟨Ideal.Quotient.mk J.toIdeal f.val, f.val, f.property, rfl⟩
    let E := IntegerCoordinateBaseChange.GradedHilbert.integerQuotientGradingBaseChangeEquiv (S := A) I d
    let x := E.symm q
    have hx : x = 0 := by
      apply TensorSaturatedCoordinates.GradedHilbert.flat_saturated_tensor_no_irrelevant_torsion I hI d A x
      intro i
      obtain ⟨k, hk⟩ := (Projective.Saturation.GradedHilbert.mem_projectiveSaturation_iff J f.property).mp hf i
      refine ⟨k, ?_⟩
      apply (Graded.BaseChange.GradedHilbert.quotientBaseChangeEquiv (S := A) I).injective
      rw [map_zero, IntegerCoordinateBaseChange.GradedHilbert.quotientBaseChangeEquiv_scalar, ← IntegerCoordinateBaseChange.GradedHilbert.integerQuotientGradingBaseChangeEquiv_val]
      change Ideal.Quotient.mk J.toIdeal (MvPolynomial.map (algebraMap R A) (X i ^ k)) *
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

theorem flat_extendedHomogeneousIdeal_saturation
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal) :
    Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I) = Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I := by
  apply HomogeneousIdeal.ext'
  intro d f hf
  change (⟨f, hf⟩ : Hilbert.Polynomial.GradedHilbert.grading A n d) ∈
    Hilbert.Polynomial.GradedHilbert.degreeRelations (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)).toIdeal d ↔
    (⟨f, hf⟩ : Hilbert.Polynomial.GradedHilbert.grading A n d) ∈ Hilbert.Polynomial.GradedHilbert.degreeRelations (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I).toIdeal d
  rw [flat_saturated_saturation_baseChange I hI d]

theorem flat_extendedHomogeneousIdeal_isSaturated
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal) :
    Hilbert.Polynomial.GradedHilbert.IsSaturated (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I).toIdeal := by
  rw [← flat_extendedHomogeneousIdeal_saturation I hI]
  exact Projective.Saturation.GradedHilbert.projectiveSaturation_isSaturated _

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.SaturationBaseChange.GradedHilbert
