import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Change
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CurvatureD

/-! # Cocycle -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric

noncomputable section

/-! Every actual metric represents the same normalized de Rham class as the original canonical metric. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {u : Holomorphic.Connecting.holomorphicUnitCohomology E M}

def Data.HolomorphicLineMetricData.normalizedCurvature (h : Data.HolomorphicLineMetricData u) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 2 :=
  Holomorphic.CurvatureD.holomorphicCurvatureChernScale • h.curvature

theorem Data.HolomorphicLineMetricData.normalizedCurvature_closed (h : Data.HolomorphicLineMetricData u) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d h.normalizedCurvature = 0 := by
  unfold Data.HolomorphicLineMetricData.normalizedCurvature
  rw [map_smul, h.curvature_closed, smul_zero]

def Data.HolomorphicLineMetricData.curvatureCocycle (h : Data.HolomorphicLineMetricData u) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) 2 :=
  ⟨h.normalizedCurvature, (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff _ 2 _).mpr h.normalizedCurvature_closed⟩

theorem Data.HolomorphicLineMetricData.normalizedCurvature_change (h k : Data.HolomorphicLineMetricData u) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Holomorphic.CurvatureD.holomorphicCurvatureChernScale • h.changePrimitive k) =
      h.normalizedCurvature - k.normalizedCurvature := by
  unfold Data.HolomorphicLineMetricData.normalizedCurvature
  rw [map_smul, ← h.curvature_change k, smul_sub]

theorem Data.HolomorphicLineMetricData.curvature_class_independent (h k : Data.HolomorphicLineMetricData u) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) 2 h.curvatureCocycle =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) 2 k.curvatureCocycle := by
  apply (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_iff_exists_succ _ 1 _ _).mpr
  exact ⟨Holomorphic.CurvatureD.holomorphicCurvatureChernScale • h.changePrimitive k, h.normalizedCurvature_change k⟩

variable [FiniteDimensional ℝ E] [CompactSpace M] [T2Space M]

theorem Cocycle.holomorphicLineCanonicalMetric_curvatureCocycle (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) :
    (Data.holomorphicLineCanonicalMetric u).curvatureCocycle = Holomorphic.CurvatureD.holomorphicLineCurvatureCocycle u :=
  Subtype.ext (congrArg (fun a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 2 => Holomorphic.CurvatureD.holomorphicCurvatureChernScale • a)
    (Curvature.holomorphicLineCanonicalMetric_curvature u))

theorem Data.HolomorphicLineMetricData.curvature_class_original (h : Data.HolomorphicLineMetricData u) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) 2 h.curvatureCocycle =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) 2 (Holomorphic.CurvatureD.holomorphicLineCurvatureCocycle u) :=
  (h.curvature_class_independent (Data.holomorphicLineCanonicalMetric u)).trans
    (congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) 2) (Cocycle.holomorphicLineCanonicalMetric_curvatureCocycle u))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric
