import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.IdealEquivalence
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Saturation

/-! # Ideal Order -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.IdealOrder.GradedHilbert

noncomputable section

/-! The correspondence between saturated homogeneous ideals and
actual projective ideal sheaves preserves and reflects containment. -/

open _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable {R : Type u} [CommRing R] {n : ℕ}

theorem homogeneousIdealOfSheaf_mono : Monotone (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf (R := R) (n := n)) := by
  intro I J h
  apply Ideal.homogeneousCore_mono
  apply iInf_mono
  intro i
  apply Ideal.comap_mono
  exact Ideal.comap_mono (h _)

theorem projectiveQuotientIdeal_mono (I J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (h : I ≤ J) :
    (Quotient.GradedHilbert.projectiveQuotientInclusion I).ker ≤ (Quotient.GradedHilbert.projectiveQuotientInclusion J).ker := by
  let U (i : Fin (n + 1)) : (Proj (Hilbert.Polynomial.GradedHilbert.grading R n)).affineOpens :=
    ⟨Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading R n) (X i),
      Proj.isAffineOpen_basicOpen (Hilbert.Polynomial.GradedHilbert.grading R n) (X i) (isHomogeneous_X R i) Nat.zero_lt_one⟩
  apply Scheme.IdealSheafData.le_of_iSup_eq_top U IdealEquivalence.GradedHilbert.coordinateBasicOpen_cover
  intro i
  apply (Ideal.comap_le_comap_iff_of_surjective (Proj.awayToSection (Hilbert.Polynomial.GradedHilbert.grading R n) (X i)).hom
    (Proj.basicOpenIsoAway (Hilbert.Polynomial.GradedHilbert.grading R n) (X i) (isHomogeneous_X R i)
      Nat.zero_lt_one).commRingCatIsoToRingEquiv.surjective _ _).mp
  rw [← IdealRecovery.GradedHilbert.projective_chart_kernel_eq I Nat.zero_lt_one (X i) (isHomogeneous_X R i),
    ← IdealRecovery.GradedHilbert.projective_chart_kernel_eq J Nat.zero_lt_one (X i) (isHomogeneous_X R i),
    IdealEquivalence.GradedHilbert.quotient_chart_kernel_eq_map, IdealEquivalence.GradedHilbert.quotient_chart_kernel_eq_map]
  exact Ideal.map_mono h

theorem projectiveQuotientIdeal_le_iff (I J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    (Quotient.GradedHilbert.projectiveQuotientInclusion I).ker ≤ (Quotient.GradedHilbert.projectiveQuotientInclusion J).ker ↔
      Saturation.GradedHilbert.projectiveSaturation I ≤ Saturation.GradedHilbert.projectiveSaturation J := by
  constructor
  · intro h
    exact homogeneousIdealOfSheaf_mono (R := R) (n := n) h
  · intro h
    have hh := projectiveQuotientIdeal_mono (Saturation.GradedHilbert.projectiveSaturation I) (Saturation.GradedHilbert.projectiveSaturation J) h
    simpa only [Saturation.GradedHilbert.projectiveSaturation_idealSheaf] using hh

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.IdealOrder.GradedHilbert
