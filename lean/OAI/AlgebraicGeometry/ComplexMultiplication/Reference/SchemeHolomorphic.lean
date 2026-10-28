import OAI.AlgebraicGeometry.ComplexPoint.Manifold
import OAI.AlgebraicGeometry.Smooth.Equidimensional
import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-! # Scheme Holomorphic -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SchemeHolomorphic

noncomputable section

/-! # Holomorphicity of actual scheme maps in the original atlas

Every target coordinate is an actual regular-section evaluation. Its pullback
is the evaluation of the pullback section, analytic in the original source chart.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoint _root_.TopologicalSpace Filter
open scoped ContDiff _root_.Manifold _root_.Topology

variable {X Y : Over (Spec (.of ℂ))}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

/-- Actual algebraic maps have analytic coordinate expressions in the unchanged original charts. -/
theorem contDiffOn_schemeMap_originalCharts (f : X ⟶ Y)
    (z : ComplexPoint.Basic.ComplexSchemePoint X) (y : ComplexPoint.Basic.ComplexSchemePoint Y) :
    ContDiffOn ℂ ω
      (fun w => ComplexPoint.Basic.ComplexSchemePoint.localChart Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) y
        (ComplexPoint.Basic.Point.map f ((ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z).symm w)))
      ((ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z).target ∩
        (ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z).symm ⁻¹'
          ComplexPoint.Basic.Point.map f ⁻¹' (ComplexPoint.Basic.ComplexSchemePoint.localChart Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) y).source) := by
  apply contDiffOn_pi.mpr
  intro i w hw
  let D := ComplexPoint.Basic.ComplexSchemePoint.localEtaleCoordinates Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) y
  have hV : ComplexPoint.Basic.Point.map f ((ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z).symm w) ∈
      ComplexPoint.Basic.Point.overOpen D.ambientCoordinateOpen := by
    have h := ComplexPoint.Basic.ComplexSchemePoint.mem_coordinateNeighborhood_of_mem_localChart_source
      Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) y _ hw.2
    simpa only [D, ComplexPoint.SmoothCoordinates.LocalEtaleCoordinates.ambientCoordinateOpen,
      Scheme.Opens.ι_image_top] using h
  have hpre : (ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z).symm w ∈
      ComplexPoint.Basic.Point.overOpen (f.left ⁻¹ᵁ D.ambientCoordinateOpen) := hV
  have ha := ComplexPoint.Basic.ComplexSchemePoint.analyticAt_localChart_symm_evaluate X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z hw.1
    (f.left ⁻¹ᵁ D.ambientCoordinateOpen)
    (f.left.app D.ambientCoordinateOpen (D.ambientCoordinateSection i)) hpre
  have hc : ContinuousAt
      (fun v => ComplexPoint.Basic.Point.map f ((ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z).symm v)) w :=
    (ComplexPoint.Basic.Point.continuousMap f).continuous.continuousAt.comp
      ((ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z).continuousAt_symm hw.1)
  have heventually : ∀ᶠ v in 𝓝 w,
      ComplexPoint.Basic.Point.map f ((ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z).symm v) ∈
        (ComplexPoint.Basic.ComplexSchemePoint.localChart Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) y).source :=
    hc ((ComplexPoint.Basic.ComplexSchemePoint.localChart Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) y).open_source.mem_nhds hw.2)
  have hcoord : AnalyticAt ℂ
      (fun v => ComplexPoint.Basic.ComplexSchemePoint.localChart Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) y
        (ComplexPoint.Basic.Point.map f ((ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z).symm v)) i) w := by
    apply ha.congr
    filter_upwards [heventually] with v hv
    exact ((ComplexPoint.Basic.ComplexSchemePoint.localChart_apply_component_eq_evaluate Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) y _ hv i).trans
      (ComplexPoint.Basic.Point.evaluate_map f D.ambientCoordinateOpen (D.ambientCoordinateSection i)
        ((ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z).symm v))).symm
  exact hcoord.contDiffAt.contDiffWithinAt

/-- Actual scheme maps are holomorphic for the original smooth complex-point manifolds. -/
theorem contMDiff_schemeMap_original (f : X ⟶ Y) :
    ContMDiff 𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ) 𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) → ℂ) ω
      (ComplexPoint.Basic.Point.map f) := by
  apply contMDiff_iff.mpr
  refine ⟨(ComplexPoint.Basic.Point.continuousMap f).continuous, ?_⟩
  intro z y
  have hX : chartAt (Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ) z = ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z := rfl
  have hY : chartAt (Fin (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) → ℂ) y = ComplexPoint.Basic.ComplexSchemePoint.localChart Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) y := rfl
  simp only [extChartAt, OpenPartialHomeomorph.extend,
    modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl, Function.comp_def,
    hX, hY, OpenPartialHomeomorph.coe_toPartialEquiv]
  exact contDiffOn_schemeMap_originalCharts f z y

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SchemeHolomorphic
