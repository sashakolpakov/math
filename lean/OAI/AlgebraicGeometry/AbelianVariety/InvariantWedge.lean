import OAI.AlgebraicGeometry.AbelianVariety.PureAverage
import OAI.AlgebraicTopology.Kunneth.ManifoldWedge
import OAI.AlgebraicTopology.Kunneth.WedgeAlgebra

/-! # Invariant Wedge -/

namespace OAI.AlgebraicGeometry.AbelianVariety.InvariantWedge.Constructions.ExteriorCohomology

noncomputable section

open scoped _root_.Manifold ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Group G] [TopologicalSpace G] [ChartedSpace E G] [LieGroup 𝓘(ℝ, E) ∞ G]
  {p q : ℕ}

theorem manifoldWedge_pullback_self (f : G → G) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ f)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G p) (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G q) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback f hf (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a b) =
      AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback f hf a) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback f hf b) := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  exact (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge_pullback (E := E) (F := E)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x) (a (f x)) (b (f x))).symm

theorem manifoldWedge_mem_invariantForms (a : InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) p)
    (b : InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) q) :
    AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a.val b.val ∈ InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) (p + q) := by
  rw [InvariantClosed.Constructions.ExteriorCohomology.mem_invariantForms_iff]
  intro g
  rw [manifoldWedge_pullback_self, (InvariantClosed.Constructions.ExteriorCohomology.mem_invariantForms_iff a.val).mp a.property g,
    (InvariantClosed.Constructions.ExteriorCohomology.mem_invariantForms_iff b.val).mp b.property g]

def invariantWedge (a : InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) p)
    (b : InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) q) : InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) (p + q) :=
  ⟨AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a.val b.val, manifoldWedge_mem_invariantForms a b⟩

theorem invariantChartEval_wedge (a : InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) p)
    (b : InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) q) :
    PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv (p + q) (invariantWedge a b) =
      AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv p a) (PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv q b) := by
  rw [PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv_apply, PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv_apply, PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv_apply]
  exact congrFun (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge_inChart a.val.val b.val.val (chartAt E (1 : G)))
    (chartAt E (1 : G) 1)

theorem invariantChartEval_symm_wedge (a : E [⋀^Fin p]→L[ℝ] ℂ)
    (b : E [⋀^Fin q]→L[ℝ] ℂ) :
    (PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv (E := E) (G := G) (p + q)).symm (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge a b) =
      invariantWedge ((PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv p).symm a) ((PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv q).symm b) := by
  apply (PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv (p + q)).injective
  rw [LinearEquiv.apply_symm_apply, invariantChartEval_wedge,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem scalarCovectorPullback_wedge (z : ℂ) (a : E [⋀^Fin p]→L[ℝ] ℂ)
    (b : E [⋀^Fin q]→L[ℝ] ℂ) :
    Analysis.DifferentialForms.Manifold.Bidegree.scalarCovectorPullback E (p + q) z (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge a b) =
      AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (Analysis.DifferentialForms.Manifold.Bidegree.scalarCovectorPullback E p z a) (Analysis.DifferentialForms.Manifold.Bidegree.scalarCovectorPullback E q z b) :=
  (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge_pullback (ContinuousLinearMap.lsmul ℝ ℂ z) a b).symm

end

end OAI.AlgebraicGeometry.AbelianVariety.InvariantWedge.Constructions.ExteriorCohomology
