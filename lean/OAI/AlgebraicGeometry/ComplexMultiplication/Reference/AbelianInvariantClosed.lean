import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.AbelianInvariantGlobal
import OAI.AlgebraicGeometry.AbelianVariety.InvariantClosed

/-! # Abelian Invariant Closed -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.AbelianInvariantClosed

noncomputable section

/-! # Closed global original holomorphic representatives of actual invariant one-forms -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] [GrpObj X]

local notation "N" =>
  (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)

/-- Commutativity of the genuine native point group follows from the original abelian scheme. -/
instance nativePointManifoldMulCommutative : IsMulCommutative (AnalyticIntrinsicAtlasRegular.NativePointManifold X) :=
  (isCommMonObj_iff_isMulCommutative (BundledAbelianBridge.originalAbelianVariety X).toOver).mp
    inferInstance (Over.mk (𝟙 (Spec (.of ℂ))))

/-- The transported actual invariant smooth form is closed. -/
theorem originalAbelianInvariantSmoothForm_closed (α : N →L[ℂ] ℂ) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (AbelianInvariantSmooth.originalAbelianInvariantSmoothForm X α) = 0 := by
  unfold AbelianInvariantSmooth.originalAbelianInvariantSmoothForm
  rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_pullback,
    AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms_closed _ (AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantSmoothForm_mem _), map_zero]

omit [Foundations.ProjectiveSpaceIs.IsProjective X.hom] [GrpObj X] in
/-- Global original holomorphic sections are determined by their actual smooth tangent values. -/
theorem originalHolomorphicSheafToGlobalSmoothForm_injective (p : ℕ) :
    Function.Injective (ReferenceSmooth.Local.originalHolomorphicSheafToGlobalSmoothForm X p) := by
  intro a b h
  apply ReferenceSmooth.Local.originalHolomorphicToSmoothSheafSection_injective X p ⊤
  have hu := congrArg (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤) h
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤
      (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal (ReferenceSmooth.Local.originalHolomorphicToSmoothSheafSection X p ⊤ a)) =
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤
      (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal (ReferenceSmooth.Local.originalHolomorphicToSmoothSheafSection X p ⊤ b)) at hu
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.onOpen_toGlobal, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.onOpen_toGlobal] at hu
  exact hu

/-- The constructed original section is closed for the unchanged original sheaf differential. -/
theorem originalAbelianInvariantGlobalSection_closed (α : N →L[ℂ] ℂ) :
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) 1).hom.app (op ⊤)
      (AbelianInvariantGlobal.originalAbelianInvariantGlobalSection X α) = 0 := by
  apply originalHolomorphicSheafToGlobalSmoothForm_injective X 2
  rw [map_zero, ← ReferenceSmooth.Local.originalHolomorphicSheafToGlobalSmoothForm_differential,
    AbelianInvariantGlobal.originalAbelianInvariantGlobalSection_smooth, originalAbelianInvariantSmoothForm_closed]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.AbelianInvariantClosed
