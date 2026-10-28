import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexChartOrientation
import OAI.AlgebraicGeometry.CycleClass.Geometric.ClosedBall

/-! # Complex Coordinate Comparison -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexCoordinateComparison

noncomputable section

/-!
# Comparison with the compact-support coordinate normalization

The centered-chart local class is identified with the coordinate point class
used by the actual closed-ball and compact-support constructions. The proof
compares the maps on the chart source, including the actual translation.
-/

open _root_.CategoryTheory
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Cycles

variable {p : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin p → ℂ) M]
variable [T1Space M]

/-- Centering the partial chart and first taking its local map then
translating produce exactly the same homomorphism. -/
theorem complexChartLocalIso_hom_eq_translation
    (e : OpenPartialHomeomorph M (Fin p → ℂ))
    (x : M) (hx : x ∈ e.source) (n : ℕ) :
    (ComplexChartOrientation.Cycles.complexChartLocalIso e x hx n).hom =
      (LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso
        (X := TopCat.of M) (Y := TopCat.of (Fin p → ℂ)) e x hx n).hom ≫
        (ClosedBall.Cycles.localTranslationHomologyIso (Fin p → ℂ) (e x) n).hom := by
  let i := LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of M) e.source x hx e.open_source n
  apply (cancel_epi i.hom).mp
  have hxc : x ∈ (CenteredChartTransition.Cycles.centeredLocalChart e x).source := by
    rw [CenteredChartTransition.Cycles.centeredLocalChart_source]
    exact hx
  change HomologicalComplex.homologyMap
      (LocalExcision.Cycles.localExcisionChainMap (TopCat.of M) (CenteredChartTransition.Cycles.centeredLocalChart e x).source x hxc) n ≫
        (LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo
          (X := TopCat.of M) (Y := TopCat.of (Fin p → ℂ))
          (CenteredChartTransition.Cycles.centeredLocalChart e x) x 0 hxc (CenteredChartTransition.Cycles.centeredLocalChart_at_point e x) n).hom =
    HomologicalComplex.homologyMap
      (LocalExcision.Cycles.localExcisionChainMap (TopCat.of M) e.source x hx) n ≫ _
  rw [LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo_source
    (X := TopCat.of M) (Y := TopCat.of (Fin p → ℂ))]
  rw [← Category.assoc, LocalChartMaps.Cycles.openPartialLocalHomology_source
    (X := TopCat.of M) (Y := TopCat.of (Fin p → ℂ)) e x hx n]
  unfold LocalChartMaps.Cycles.injectiveLocalHomologyMapTo LocalChartMaps.Cycles.injectiveLocalHomologyMap ClosedBall.Cycles.localTranslationHomologyIso
  rw [LocalHomology.Cycles.relativeSingularHomologyIso_hom]
  rw [LocalHomology.Cycles.relativeSingularHomologyMap_comp]
  apply LocalChartMaps.Cycles.relativeSingularHomologyMap_congr
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro u
  change e u.val + -(e x) = e u.val - e x
  exact (sub_eq_add_neg _ _).symm

variable [IsManifold 𝓘(ℂ, Fin p → ℂ) 1 M]

/-- An actual complex atlas chart takes the canonical manifold local class
to the same coordinate point class used by compact-support fundamental
classes. -/
theorem complexCanonicalLocalClass_chart
    (e : OpenPartialHomeomorph M (Fin p → ℂ)) (he : e ∈ atlas (Fin p → ℂ) M)
    (x : M) (hx : x ∈ e.source) :
    (LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso
      (X := TopCat.of M) (Y := TopCat.of (Fin p → ℂ)) e x hx (2 * p)).hom
        (ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x) =
      ClosedBall.Cycles.complexCoordinatePointClass p (e x) := by
  apply (ConcreteCategory.bijective_of_isIso
    (ClosedBall.Cycles.localTranslationHomologyIso (Fin p → ℂ) (e x) (2 * p)).hom).1
  change ((LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso
      (X := TopCat.of M) (Y := TopCat.of (Fin p → ℂ)) e x hx (2 * p)).hom ≫
      (ClosedBall.Cycles.localTranslationHomologyIso (Fin p → ℂ) (e x) (2 * p)).hom)
        (ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x) = _
  rw [← complexChartLocalIso_hom_eq_translation,
    ComplexChartOrientation.Cycles.complexChartLocalIso_canonical e he x hx, ClosedBall.Cycles.complexCoordinatePointClass_to_origin]
  rfl

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexCoordinateComparison
