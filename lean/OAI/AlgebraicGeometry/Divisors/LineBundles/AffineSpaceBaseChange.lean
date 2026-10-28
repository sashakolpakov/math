import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SpaceChartBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.PulledSupport

/-! # Affine Space Base Change -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-! # LineBundleCycles: genuine affine-space bundle charts persist over arbitrary closed or singular bases -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

theorem Affine.SpaceChartBaseChange.BundleCycles.HasAffineSpaceCharts.baseChange {E X Y : Scheme.{0}} {p : E ⟶ X}
    (h : Affine.SpaceChartBaseChange.BundleCycles.HasAffineSpaceCharts p) (g : Y ⟶ X) : Affine.SpaceChartBaseChange.BundleCycles.HasAffineSpaceCharts (pullback.snd p g) := by
  intro y
  obtain ⟨U, i, ι, hι, j, hi, hj, hy, hs⟩ := h (g y)
  let := hi
  refine ⟨pullback g i, pullback.fst g i, ι, hι,
    Affine.SpaceChartBaseChange.BundleCycles.affineSpaceChartBaseChangeMap p g i ι j hs, inferInstance, inferInstance, ?_,
    Affine.SpaceChartBaseChange.BundleCycles.affineSpaceChartBaseChange_isPullback p g i ι j hs⟩
  obtain ⟨u, hu⟩ := hy
  obtain ⟨v, hv, _⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback g i) y u hu.symm
  exact ⟨v, hv⟩

theorem AffineSpaceBaseChange.BundleCycles.integralPulledSupport_hasAffineSpaceCharts {E X : Scheme.{0}} (p : E ⟶ X)
    (h : Affine.SpaceChartBaseChange.BundleCycles.HasAffineSpaceCharts p) (W : TopologicalSpace.IrreducibleCloseds X) :
    Affine.SpaceChartBaseChange.BundleCycles.HasAffineSpaceCharts (Integral.PulledSupport.BundleCycles.integralPulledSupportProjection p W) :=
  h.baseChange (CycleClass.Geometric.GenericPoint.reducedSupportι W)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
