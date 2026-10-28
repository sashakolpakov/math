import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.IntegerQuotient
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.IdealEquivalence
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EventualIrrelevantTorsion

/-! # Saturation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Saturation.GradedHilbert

noncomputable section

/-! Saturation by the projective ideal sheaf preserves all sufficiently high coordinate degrees. -/

open _root_.MvPolynomial _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.EventualIrrelevantTorsion.ProjectiveCech

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

def projectiveSaturation (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n) :=
  ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I).ker

theorem projectiveSaturation_isSaturated (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    Hilbert.Polynomial.GradedHilbert.IsSaturated (projectiveSaturation I).toIdeal := ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf_saturated _

theorem mem_projectiveSaturation_iff (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n} {d : ℕ} (hf : f.IsHomogeneous d) :
    f ∈ (projectiveSaturation I).toIdeal ↔
      ∀ i : Fin (n + 1), ∃ k : ℕ, X i ^ k * f ∈ I.toIdeal := by
  change f ∈ (ChartHomogeneousIdeal.GradedHilbert.chartHomogeneousIdeal _).toIdeal ↔ _
  rw [ChartHomogeneousIdeal.GradedHilbert.mem_chartHomogeneousIdeal _ hf]
  apply forall_congr'
  intro i
  rw [ChartHomogeneousIdeal.GradedHilbert.projectiveChartIdeal, ← IdealRecovery.GradedHilbert.projective_chart_kernel_eq I Nat.zero_lt_one (X i)
    (isHomogeneous_X R i), Dehomogenization.GradedHilbert.dehomogenize_homogeneous i hf]
  exact IdealRecovery.GradedHilbert.quotient_coordinateFraction_eq_zero_iff I i d ⟨f, hf⟩

theorem le_projectiveSaturation (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    I ≤ projectiveSaturation I := by
  intro f hf
  apply (Ideal.IsHomogeneous.mem_iff (Hilbert.Polynomial.GradedHilbert.grading R n) (projectiveSaturation I).isHomogeneous).mpr
  intro d
  have hI := (Ideal.IsHomogeneous.mem_iff (Hilbert.Polynomial.GradedHilbert.grading R n) I.isHomogeneous).mp hf d
  exact (mem_projectiveSaturation_iff I (DirectSum.decompose (Hilbert.Polynomial.GradedHilbert.grading R n) f d).property).mpr
    (fun _ => ⟨0, by simpa only [pow_zero, one_mul] using hI⟩)

theorem projectiveSaturation_idealSheaf (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (projectiveSaturation I)).ker =
      (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I).ker := IdealEquivalence.GradedHilbert.projectiveQuotient_homogeneousIdealOfSheaf _

theorem projectiveSaturation_eq_of_saturated (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal) : projectiveSaturation I = I :=
  ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf_projectiveQuotient I hI

theorem projectiveSaturation_idempotent (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    projectiveSaturation (projectiveSaturation I) = projectiveSaturation I :=
  projectiveSaturation_eq_of_saturated _ (projectiveSaturation_isSaturated I)

theorem projectiveSaturation_eventual_degreeRelations [IsNoetherianRing R]
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    ∃ N : ℕ, ∀ d ≥ N,
      Hilbert.Polynomial.GradedHilbert.degreeRelations (projectiveSaturation I).toIdeal d = Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d := by
  obtain ⟨N, hN⟩ := EventualIrrelevantTorsion.ProjectiveCech.eventual_no_irrelevant_torsion (σ := Fin (n + 1))
    R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I)
  refine ⟨N, fun d hd => ?_⟩
  apply le_antisymm
  · intro f hf
    change f.val ∈ I.toIdeal
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hN (d : ℤ) (by exact_mod_cast hd) (Ideal.Quotient.mk I.toIdeal f.val)
    · rw [Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading_nat]
      exact ⟨f.val, f.property, rfl⟩
    · intro i
      obtain ⟨k, hk⟩ := (mem_projectiveSaturation_iff I f.property).mp hf i
      refine ⟨k, ?_⟩
      change Ideal.Quotient.mk I.toIdeal (X i ^ k * f.val) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hk
  · intro f hf
    exact (le_projectiveSaturation I) hf

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Saturation.GradedHilbert
