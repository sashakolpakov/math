import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FractionFieldHomogeneousContraction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SaturatedFlatCoordinateTorsion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Saturation

/-! # Saturated Flat Generic Uniqueness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.SaturatedFlatGenericUniqueness.GradedHilbert

noncomputable section

/-! Saturated flat projective ideals over an integral coefficient ring
are uniquely determined by their scheme-theoretic generic fibers. -/

open _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] {n : ℕ}

theorem saturatedFlat_contracted_generic (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
    [Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))] :
    ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) I) = I :=
  FractionFieldHomogeneousContraction.GradedHilbert.contracted_extended_eq_of_degree_torsionFree I (SaturatedFlatCoordinateTorsion.GradedHilbert.saturatedFlat_degree_isTorsionFree I hI)

theorem saturatedFlat_mem_of_generic_saturation
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
    [Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))]
    (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (d : ℕ) (hf : f.IsHomogeneous d)
    (h : MvPolynomial.map (algebraMap R K) f ∈
      (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) I)).toIdeal) : f ∈ I.toIdeal := by
  apply hI.mem_of_variable_powers f d hf
  intro i
  obtain ⟨k, hk⟩ := (Projective.Saturation.GradedHilbert.mem_projectiveSaturation_iff _ (hf.map (algebraMap R K))).mp h i
  refine ⟨k, ?_⟩
  have hm : X i ^ k * f ∈ (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) I)).toIdeal := by
    change MvPolynomial.map (algebraMap R K) (X i ^ k * f) ∈ (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) I).toIdeal
    simpa only [map_mul, map_pow, MvPolynomial.map_X] using hk
  rwa [saturatedFlat_contracted_generic (K := K) I hI] at hm

theorem saturatedFlat_eq_of_generic_saturation
    (I J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal) (hJ : Hilbert.Polynomial.GradedHilbert.IsSaturated J.toIdeal)
    [Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))] [Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading J))]
    (h : Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) I) =
      Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) J)) : I = J := by
  apply HomogeneousIdeal.ext'
  intro d f hf
  change f ∈ I.toIdeal ↔ f ∈ J.toIdeal
  constructor
  · intro hfI
    apply saturatedFlat_mem_of_generic_saturation (K := K) J hJ f d hf
    rw [← h]
    exact Projective.Saturation.GradedHilbert.le_projectiveSaturation _ (Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap R K)) hfI)
  · intro hfJ
    apply saturatedFlat_mem_of_generic_saturation (K := K) I hI f d hf
    rw [h]
    exact Projective.Saturation.GradedHilbert.le_projectiveSaturation _ (Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap R K)) hfJ)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.SaturatedFlatGenericUniqueness.GradedHilbert
