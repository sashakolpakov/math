import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGauge
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OverPullbackOpenCover

/-! # Literal Affine Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.LiteralAffineCover

noncomputable section

/-! Replace the original affine-cover presentations by their literal
open subfamilies. Their actual inclusions cover the family and base-change
to a cover of its actual special fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k)))) (U : X.left.AffineOpenCover)

def dualFamilyLiteralAffineCover : X.left.OpenCover where
  I₀ := U.I₀
  X i := (OpenChart.dualFamilyOpenObject k X (ChartGauge.dualFamilyChartAffineOpen k X U i).1).left
  f i := (OpenChart.dualFamilyOpenInclusion k X (ChartGauge.dualFamilyChartAffineOpen k X U i).1).left
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, ?_⟩
    · intro x
      refine ⟨U.idx x, ?_⟩
      change x ∈ Set.range ((ChartGauge.dualFamilyChartAffineOpen k X U (U.idx x)).1.ι)
      rw [Scheme.Opens.range_ι]
      exact U.covers x
    · intro i
      exact OpenChart.dualFamilyOpenInclusion_open k X (ChartGauge.dualFamilyChartAffineOpen k X U i).1

local instance dualLiteralAffineCover_inclusionOpen (i : U.I₀) :
    IsOpenImmersion (OpenChart.dualFamilyOpenInclusion k X (ChartGauge.dualFamilyChartAffineOpen k X U i).1).left :=
  OpenChart.dualFamilyOpenInclusion_open k X (ChartGauge.dualFamilyChartAffineOpen k X U i).1

theorem dualFamilyLiteralAffineCover_covers (x : X.left) :
    ∃ i : U.I₀, x ∈ (OpenChart.dualFamilyOpenInclusion k X (ChartGauge.dualFamilyChartAffineOpen k X U i).1).left.opensRange := by
  refine ⟨U.idx x, ?_⟩
  change x ∈ Set.range ((ChartGauge.dualFamilyChartAffineOpen k X U (U.idx x)).1.ι)
  rw [Scheme.Opens.range_ι]
  exact U.covers x

def dualFamilyReducedAffineCover : ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X).left.OpenCover :=
  OverPullbackOpenCover.overPullbackOpenCover (Smooth.AffineDualProduct.dualBaseReduction k)
    (fun i : U.I₀ => OpenChart.dualFamilyOpenObject k X (ChartGauge.dualFamilyChartAffineOpen k X U i).1)
    (fun i => OpenChart.dualFamilyOpenInclusion k X (ChartGauge.dualFamilyChartAffineOpen k X U i).1)
    (dualFamilyLiteralAffineCover_covers k X U)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.LiteralAffineCover
