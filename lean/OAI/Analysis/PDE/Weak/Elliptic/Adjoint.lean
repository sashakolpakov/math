import OAI.Analysis.PDE.Weak.Elliptic.L2
import OAI.Analysis.PDE.Weak.Elliptic.TestSupport

noncomputable section
open Set _root_.MeasureTheory InnerProductSpace
namespace OAI.Analysis.PDE.Weak

variable {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem inner_differenceQuotientL2 (μ : Measure X) [μ.IsAddRightInvariant]
    (v : X) (h : ℝ) (u w : Lp V 2 μ) :
    inner ℝ (differenceQuotientL2 μ v h u) w =
      -inner ℝ u (differenceQuotientL2 μ v (-h) w) := by
  calc
    _ = ∫ x, inner ℝ (differenceQuotient v h u x) (w x) ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [coe_differenceQuotientL2 μ v h u] with x hx
      rw [hx]
    _ = -(∫ x, inner ℝ (u x) (differenceQuotient v (-h) w x) ∂μ) := by
      apply integral_differenceQuotient_inner
      · exact integrable_inner_of_memLp (Lp.memLp u) (Lp.memLp w)
      · exact integrable_inner_of_memLp
          ((Lp.memLp u).comp_measurePreserving (measurePreserving_add_right μ (h • v)))
          (Lp.memLp w)
    _ = _ := by
      rw [L2.inner_def]
      congr 1
      apply integral_congr_ae
      filter_upwards [coe_differenceQuotientL2 μ v (-h) w] with x hx
      rw [hx]

end OAI.Analysis.PDE.Weak
