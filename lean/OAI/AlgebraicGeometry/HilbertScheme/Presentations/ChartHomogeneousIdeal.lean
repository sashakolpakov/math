import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Dehomogenization

/-! # Chart Homogeneous Ideal -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert

noncomputable section

/-!
The saturated homogeneous ideal determined by ideals on all standard
projective charts. The construction applies to actual ideal sheaves and
recovers a saturated ideal from its associated projective closed immersion.
-/

open _root_.MvPolynomial _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

abbrev ChartIdeals (R : Type u) [CommRing R] (n : ℕ) :=
  ∀ i : Fin (n + 1), Ideal (HomogeneousLocalization.Away (Hilbert.Polynomial.GradedHilbert.grading R n) (X i))

def chartHomogeneousIdeal (J : ChartIdeals R n) : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n) :=
  (⨅ i, (J i).comap (Dehomogenization.GradedHilbert.dehomogenize i)).homogeneousCore (Hilbert.Polynomial.GradedHilbert.grading R n)

theorem mem_chartHomogeneousIdeal (J : ChartIdeals R n)
    {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n} {d : ℕ} (hf : f.IsHomogeneous d) :
    f ∈ (chartHomogeneousIdeal J).toIdeal ↔ ∀ i, Dehomogenization.GradedHilbert.dehomogenize i f ∈ J i := by
  constructor
  · intro h
    have h' := Ideal.toIdeal_homogeneousCore_le (Hilbert.Polynomial.GradedHilbert.grading R n)
      (⨅ i, (J i).comap (Dehomogenization.GradedHilbert.dehomogenize i)) h
    simpa only [Ideal.mem_iInf, Ideal.mem_comap] using h'
  · intro h
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨d, hf⟩
      (by simpa only [Ideal.mem_iInf, Ideal.mem_comap] using h)

theorem chartHomogeneousIdeal_saturated (J : ChartIdeals R n) :
    Hilbert.Polynomial.GradedHilbert.IsSaturated (chartHomogeneousIdeal J).toIdeal := by
  intro f d hf h
  obtain ⟨m, hm⟩ := h
  apply (mem_chartHomogeneousIdeal J hf).mpr
  intro i
  have hg : (X (R := R) i ^ m).IsHomogeneous m := by
    simpa only [one_mul] using (isHomogeneous_X R i).pow m
  have hprod := (mem_chartHomogeneousIdeal J (hg.mul hf)).mp (hm _ hg) i
  simpa only [map_mul, map_pow, Dehomogenization.GradedHilbert.dehomogenize_self, one_pow, one_mul] using hprod

def projectiveChartIdeal (J : (Proj (Hilbert.Polynomial.GradedHilbert.grading R n)).IdealSheafData) : ChartIdeals R n :=
  fun i => (J.ideal ⟨Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading R n) (X i),
    Proj.isAffineOpen_basicOpen (Hilbert.Polynomial.GradedHilbert.grading R n) (X i) (isHomogeneous_X R i) Nat.zero_lt_one⟩).comap
      (Proj.awayToSection (Hilbert.Polynomial.GradedHilbert.grading R n) (X i)).hom

def homogeneousIdealOfSheaf (J : (Proj (Hilbert.Polynomial.GradedHilbert.grading R n)).IdealSheafData) :
    HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n) := chartHomogeneousIdeal (projectiveChartIdeal J)

theorem homogeneousIdealOfSheaf_saturated (J : (Proj (Hilbert.Polynomial.GradedHilbert.grading R n)).IdealSheafData) :
    Hilbert.Polynomial.GradedHilbert.IsSaturated (homogeneousIdealOfSheaf J).toIdeal := chartHomogeneousIdeal_saturated _

theorem homogeneousIdealOfSheaf_projectiveQuotient (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal) :
    homogeneousIdealOfSheaf (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I).ker = I := by
  apply HomogeneousIdeal.ext'
  intro d f hf
  change f ∈ (chartHomogeneousIdeal _).toIdeal ↔ f ∈ I.toIdeal
  rw [mem_chartHomogeneousIdeal _ hf]
  have hi (i : Fin (n + 1)) :
      Dehomogenization.GradedHilbert.dehomogenize i f ∈ projectiveChartIdeal (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I).ker i ↔
        ∃ k : ℕ, X i ^ k * f ∈ I.toIdeal := by
    rw [projectiveChartIdeal, ← Projective.IdealRecovery.GradedHilbert.projective_chart_kernel_eq I Nat.zero_lt_one (X i)
      (isHomogeneous_X R i), Dehomogenization.GradedHilbert.dehomogenize_homogeneous i hf]
    exact Projective.IdealRecovery.GradedHilbert.quotient_coordinateFraction_eq_zero_iff I i d ⟨f, hf⟩
  simp_rw [hi]
  exact ⟨fun h => hI.mem_of_variable_powers f d hf h,
    fun h i => ⟨0, by simpa only [pow_zero, one_mul] using h⟩⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert
