import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Saturation

/-! # Chart Ideals -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.ChartIdeals.GradedHilbert

noncomputable section

/-! Projective saturation is determined by the actual dehomogenized
ideals on the finite standard cover. -/

open _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable {R : Type u} [CommRing R] {n : ℕ}

theorem mem_projectiveSaturation_iff_dehomogenized (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n} {d : ℕ} (hf : f.IsHomogeneous d) :
    f ∈ (Projective.Saturation.GradedHilbert.projectiveSaturation I).toIdeal ↔ ∀ i : Fin (n + 1), Dehomogenization.GradedHilbert.dehomogenize i f ∈ I.toIdeal.map (Dehomogenization.GradedHilbert.dehomogenize i) := by
  change f ∈ (ChartHomogeneousIdeal.GradedHilbert.chartHomogeneousIdeal _).toIdeal ↔ _
  rw [ChartHomogeneousIdeal.GradedHilbert.mem_chartHomogeneousIdeal _ hf]
  apply forall_congr'
  intro i
  rw [ChartHomogeneousIdeal.GradedHilbert.projectiveChartIdeal, ← Projective.IdealRecovery.GradedHilbert.projective_chart_kernel_eq I Nat.zero_lt_one (X i)
    (isHomogeneous_X R i), Projective.IdealEquivalence.GradedHilbert.quotient_chart_kernel_eq_map]

theorem projectiveSaturation_eq_of_dehomogenized (I J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (h : ∀ i : Fin (n + 1), I.toIdeal.map (Dehomogenization.GradedHilbert.dehomogenize i) = J.toIdeal.map (Dehomogenization.GradedHilbert.dehomogenize i)) :
    Projective.Saturation.GradedHilbert.projectiveSaturation I = Projective.Saturation.GradedHilbert.projectiveSaturation J := by
  apply HomogeneousIdeal.ext'
  intro d f hf
  change f ∈ (Projective.Saturation.GradedHilbert.projectiveSaturation I).toIdeal ↔ f ∈ (Projective.Saturation.GradedHilbert.projectiveSaturation J).toIdeal
  rw [mem_projectiveSaturation_iff_dehomogenized I hf, mem_projectiveSaturation_iff_dehomogenized J hf]
  exact forall_congr' (fun i => by rw [h i])

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.ChartIdeals.GradedHilbert
