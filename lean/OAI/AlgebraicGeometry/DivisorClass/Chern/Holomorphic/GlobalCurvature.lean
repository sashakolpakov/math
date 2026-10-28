import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CurvatureOverlap
import OAI.Analysis.DifferentialForms.Manifold.ManifoldSheaf
import OAI.Analysis.DifferentialForms.Manifold.CovectorAction

/-! # Global Curvature -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.GlobalCurvature

noncomputable section

/-! Gluing the actual local Hermitian curvature forms gives a global closed (1,1) form. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M] [T2Space M]
  [IsManifold 𝓘(ℂ, E) ∞ M] (u : Connecting.holomorphicUnitCohomology E M)

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [CompactSpace M] [T2Space M] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem holomorphicLineCurvature_cover : ((⊤ : Opens M) : Set M) ⊆
    ⋃ i : M, (CohomologyTransitions.holomorphicCohomologyDomain E M u i : Set M) := by
  intro x _
  exact mem_iUnion.mpr ⟨x, (CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x⟩

theorem holomorphicLineCurvature_compatible :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.Compatible (HolomorphicLine.LocalCurvature.holomorphicLineLocalCurvatureForm u) :=
  (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.compatible_iff_restrict _).mpr (CurvatureOverlap.holomorphicLineLocalCurvatureForm_overlap u)

def holomorphicLineGlobalCurvatureSection : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (⊤ : Opens M) 2 :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.glue (fun _ => le_top) (holomorphicLineCurvature_cover u)
    (HolomorphicLine.LocalCurvature.holomorphicLineLocalCurvatureForm u) (holomorphicLineCurvature_compatible u)

def holomorphicLineGlobalCurvature : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 2 :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal (holomorphicLineGlobalCurvatureSection u)

theorem holomorphicLineGlobalCurvature_onOpen (i : M) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (CohomologyTransitions.holomorphicCohomologyDomain E M u i) (holomorphicLineGlobalCurvature u) =
      HolomorphicLine.LocalCurvature.holomorphicLineLocalCurvatureForm u i := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  change holomorphicLineGlobalCurvature u x.val = HolomorphicLine.LocalCurvature.holomorphicLineLocalCurvatureForm u i x
  rw [holomorphicLineGlobalCurvature, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal_apply]
  exact Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.glue_apply (fun _ => le_top) (holomorphicLineCurvature_cover u)
    (HolomorphicLine.LocalCurvature.holomorphicLineLocalCurvatureForm u) (holomorphicLineCurvature_compatible u) ⟨x.val, mem_univ x.val⟩ i x.property

theorem holomorphicLineGlobalCurvature_closed : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (holomorphicLineGlobalCurvature u) = 0 := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  have h : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (CohomologyTransitions.holomorphicCohomologyDomain E M u x)
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (holomorphicLineGlobalCurvature u)) = 0 := by
    rw [← Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen_d, holomorphicLineGlobalCurvature_onOpen,
      HolomorphicLine.LocalCurvature.holomorphicLineLocalCurvatureForm_closed]
  exact congrArg (fun a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (CohomologyTransitions.holomorphicCohomologyDomain E M u x) 3 =>
    a ⟨x, (CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x⟩) h

theorem holomorphicLineGlobalCurvature_type :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 1 1 (holomorphicLineGlobalCurvature u).val := by
  intro e he y hy
  let i := e.symm y
  have hi : e.symm y ∈ CohomologyTransitions.holomorphicCohomologyDomain E M u i :=
    (CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain i
  have hc : (HolomorphicLine.LocalCurvature.holomorphicLineLocalCurvatureForm u i).extension.inChart e y =
      (holomorphicLineGlobalCurvature u).val.inChart e y := by
    rw [← holomorphicLineGlobalCurvature_onOpen u i]
    unfold Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
    rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply _ ⟨e.symm y, hi⟩]
    rfl
  rw [← hc]
  exact HolomorphicLine.LocalCurvature.holomorphicLineLocalCurvatureForm_type u i e he y ⟨hy, hi⟩

theorem holomorphicLineGlobalCurvature_tangentType :
    Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree E M 1 1 (holomorphicLineGlobalCurvature u).val :=
  (Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree _).mp (holomorphicLineGlobalCurvature_type u)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.GlobalCurvature
