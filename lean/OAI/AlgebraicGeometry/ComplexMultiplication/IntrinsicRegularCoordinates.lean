import OAI.AlgebraicGeometry.ComplexMultiplication.RegularSectionBridge
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold
import OAI.AlgebraicGeometry.ComplexPoint.Manifold

/-! # Intrinsic Regular Coordinates -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicRegularCoordinates

noncomputable section

/-! # The genuine regular functions defining the native chart coordinates

Native chart coordinates are ratios of evaluations of actual sections on
their affine open. These same evaluations are analytic in the original atlas.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoint _root_.TopologicalSpace
open scoped ContDiff

/-- Every actual native affine chart has the displayed ambient regular-function coordinates. -/
theorem nativeAffineChart_regularCoordinates (X : Over (Spec (.of ℂ)))
    (U : X.left.Opens) (hU : IsAffineOpen U) {n : ℕ}
    (e : OpenPartialHomeomorph
      (Foundations.Scheme.AffineComplexPoints.affineComplexPoints
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) n) :
    let c := ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) e
    ∃ g : Γ(X.left, U), (∀ q ∈ c.source, ComplexPoint.Basic.Point.evaluate U g q ≠ 0) ∧
      ∀ i : Fin n, ∃ (a : Γ(X.left, U)) (k : ℕ),
        ∀ q ∈ c.source, c q i = ComplexPoint.Basic.Point.evaluate U a q / (ComplexPoint.Basic.Point.evaluate U g q) ^ k := by
  obtain ⟨g, hg, hcoords⟩ := he.2
  refine ⟨g, ?_, ?_⟩
  · rintro q ⟨x, hx, rfl⟩
    intro hzero
    exact hg x hx ((RegularSectionBridge.evaluate_nativeAffineOpenPoint X U hU x g).symm.trans hzero)
  · intro i
    obtain ⟨a, k, hcoord⟩ := hcoords i
    refine ⟨a, k, ?_⟩
    rintro q ⟨x, hx, rfl⟩
    rw [ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme_apply]
    exact (hcoord x hx).trans (congrArg₂ (fun v w : ℂ => v / w ^ k)
      (RegularSectionBridge.evaluate_nativeAffineOpenPoint X U hU x a).symm
      (RegularSectionBridge.evaluate_nativeAffineOpenPoint X U hU x g).symm)

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

/-- Evaluation of an actual localization ratio is analytic in the unchanged original atlas. -/
theorem contDiffOn_originalChart_regularRatio
    (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
    (z : ComplexPoint.Basic.ComplexSchemePoint X) (U : X.left.Opens) (a g : Γ(X.left, U)) (k : ℕ) :
    ContDiffOn ℂ ω
      (fun w => ComplexPoint.Basic.Point.evaluate U a ((ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z).symm w) /
        (ComplexPoint.Basic.Point.evaluate U g ((ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z).symm w)) ^ k)
      {w | w ∈ (ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z).target ∧
        (ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z).symm w ∈ ComplexPoint.Basic.Point.overOpen U ∧
        ComplexPoint.Basic.Point.evaluate U g ((ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z).symm w) ≠ 0} := by
  intro w hw
  have ha := ComplexPoint.Basic.ComplexSchemePoint.analyticAt_localChart_symm_evaluate X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z hw.1 U a hw.2.1
  have hg := ComplexPoint.Basic.ComplexSchemePoint.analyticAt_localChart_symm_evaluate X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z hw.1 U g hw.2.1
  exact (ha.div (hg.pow k) (pow_ne_zero k hw.2.2)).contDiffAt.contDiffWithinAt

end

end OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicRegularCoordinates
