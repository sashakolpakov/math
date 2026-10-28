import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealModelForms
import OAI.AlgebraicTopology.FundamentalClass.ChartLocalEvaluation

/-! # Integral Evaluation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntegralEvaluation.CM

noncomputable section

/-! ThetaCycle: actual integration against any integral top cycle whose local
restriction is the geometric chart simplex class. The input concerns only
the local homology restriction of that cycle. -/

open _root_.CategoryTheory Opposite Set _root_.MeasureTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.FundamentalClass.ChartLocalEvaluation.IntegrationConstruction
open scoped Simplicial _root_.Manifold ContDiff

variable {d : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M]

def integralCycleEvaluation
    (z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of M)).homology d) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d →ₗ[ℂ] ℂ :=
  ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℂ ℂ) (TopCat.of M) d).flip
    (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℂ) (TopCat.of M) d z)).comp
    (AlgebraicTopology.FundamentalClass.TopEvaluation.IntegrationConstruction.topIntegrationClass d M)

variable [T2Space M]

theorem integral_cycle_evaluation_small_chart
    (z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of M)).homology d)
    (e : OpenPartialHomeomorph M (Fin d → ℝ)) (he : e ∈ atlas (Fin d → ℝ) M)
    (K : Set M) (hK : IsCompact K) (hKs : K ⊆ e.source)
    (hchart : HomologicalComplex.homologyMap (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) Kᶜ) d z =
      AlgebraicTopology.FundamentalClass.IntegrationOrientation.Geometry.chartCompactClass e K hK hKs)
    (a : Fin d → ℝ) (r : ℝ) (hr : 0 < r) (hKi : e '' K ⊆ AlgebraicTopology.FundamentalClass.AffineOrientation.IntegrationConstruction.affineInterior d a r)
    (g : (Fin d → ℝ) → M) (hg : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ∞ g)
    (hsource : ∀ x, x + AlgebraicTopology.FundamentalClass.SimplexGeometry.IntegrationConstruction.simplexBarycenter d ∈ AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes.unitCube d → g x ∈ e.source)
    (hcoords : ∀ x, x + AlgebraicTopology.FundamentalClass.SimplexGeometry.IntegrationConstruction.simplexBarycenter d ∈ AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes.unitCube d →
      e (g x) = AlgebraicTopology.FundamentalClass.AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r x)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d) (hform : ∀ x, x ∉ K → form.val x = 0) :
    integralCycleEvaluation z form =
      ∫ y in AlgebraicTopology.FundamentalClass.AffineOrientation.IntegrationConstruction.affineInterior d a r, form.val.inChart e y (Pi.basisFun ℝ (Fin d)) := by
  let σ : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex (Fin d → ℝ) M).toSSet _⦋d⦌ :=
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothSingularMap (Fin d → ℝ) (Fin d → ℝ) g hg).app _ (AlgebraicTopology.FundamentalClass.SimplexGeometry.IntegrationConstruction.positiveSmoothSimplex d)
  have hσsource : ∀ t, (TopCat.of M).toSSetObjEquiv (op ⦋d⦌) σ.val t ∈ e.source := by
    intro t
    exact hsource (AlgebraicTopology.FundamentalClass.LocalSimplex.IntegrationGeometry.positiveSimplex d t) (AlgebraicTopology.FundamentalClass.ChartIntegral.IntegrationConstruction.positiveSimplex_shift_mem_cube d t)
  have hσcoords : ∀ t, e ((TopCat.of M).toSSetObjEquiv (op ⦋d⦌) σ.val t) =
      AlgebraicTopology.FundamentalClass.AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r (AlgebraicTopology.FundamentalClass.LocalSimplex.IntegrationGeometry.positiveSimplex d t) := by
    intro t
    exact hcoords (AlgebraicTopology.FundamentalClass.LocalSimplex.IntegrationGeometry.positiveSimplex d t) (AlgebraicTopology.FundamentalClass.ChartIntegral.IntegrationConstruction.positiveSimplex_shift_mem_cube d t)
  have hfaces := AlgebraicTopology.FundamentalClass.AffineCycle.IntegrationConstruction.chartSimplex_faces_avoid (X := TopCat.of M) e K a r hr hKi σ.val hσcoords
  let U : Opens M := ⟨Kᶜ, hK.isClosed.isOpen_compl⟩
  have hclass : (1 : ℤ) • AlgebraicTopology.FundamentalClass.ProjectedClasses.IntegrationConstruction.projectedClass (TopCat.of M) U d
      (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (TopCat.of M)) σ.val)
      (AlgebraicTopology.FundamentalClass.SimplexCycles.IntegrationConstruction.integralSimplex_relative_cycle _ _ d σ.val hfaces) =
      HomologicalComplex.homologyMap (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) U) d z := by
    rw [one_smul]
    exact (AlgebraicTopology.FundamentalClass.AffineCycle.IntegrationConstruction.chartProjectedSimplex_eq_chartCompactClass (X := TopCat.of M)
      e K hK hKs a r hr hKi σ.val hσsource hσcoords).trans hchart.symm
  have heval := AlgebraicTopology.FundamentalClass.RelativeSimplexEvaluation.IntegrationConstruction.evaluation_on_integral_relative_simplex (Fin d → ℝ) M U d
    (AlgebraicTopology.FundamentalClass.TopEvaluation.IntegrationConstruction.closedTopForm d M form) (fun x => hform x x.property)
    (AlgebraicTopology.FundamentalClass.TopEvaluation.IntegrationConstruction.topIntegrationClass d M form) (AlgebraicTopology.FundamentalClass.TopEvaluation.IntegrationConstruction.topIntegrationClass_restriction d M form)
    z σ hfaces 1 hclass
  have heval' : integralCycleEvaluation z form = AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration σ form := by
    simpa only [integralCycleEvaluation, AlgebraicTopology.FundamentalClass.TopEvaluation.IntegrationConstruction.closedTopForm, LinearMap.comp_apply,
      LinearMap.flip_apply, LinearMap.codRestrict_apply, LinearMap.id_apply, one_smul] using! heval
  exact heval'.trans (AlgebraicTopology.FundamentalClass.ChartIntegral.IntegrationConstruction.smoothSimplexIntegration_affine_chart g hg e he a r hr
    (fun x hx => hsource x (AlgebraicTopology.FundamentalClass.ChartIntegral.IntegrationConstruction.positiveInterior_shift_mem_cube d x hx))
    (fun x hx => hcoords x (AlgebraicTopology.FundamentalClass.ChartIntegral.IntegrationConstruction.positiveInterior_shift_mem_cube d x hx)) form)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntegralEvaluation.CM
