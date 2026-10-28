import OAI.Analysis.DifferentialForms.Manifold.BidegreeInvariant

/-! # Covector Purity -/

namespace OAI.RepresentationTheory.Theta.Geometric.Complex.CovectorPurity

noncomputable section

/-! A field of complex-linear tangent covectors has actual manifold
bidegree (1,0), with respect to the genuine complex atlas. -/

set_option backward.isDefEq.respectTransparency false
open OAI.Analysis.DifferentialForms.Manifold.BidegreeInvariant
open scoped _root_.Manifold ContDiff

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℂ, E) ∞ M]

def complexCovectorRawForm (c : M → E →L[ℂ] ℂ) : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M 1 :=
  fun x => Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector E (c x)

theorem complexCovectorRawForm_preferred (c : M → E →L[ℂ] ℂ) (x : M) :
    (complexCovectorRawForm c).inChart (chartAt E x) (chartAt E x x) =
      Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector E (c x) := by
  let : IsManifold 𝓘(ℝ, E) ∞ M := Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth
  have hd := mfderivWithin_range_extChartAt_symm (I := 𝓘(ℝ, E)) (x := x)
  have hd' : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x).symm (chartAt E x x) =
      ContinuousLinearMap.id ℝ E := by
    simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_def, id_eq, Set.range_id,
      mfderivWithin_univ] at hd
    exact hd
  ext v
  change c ((chartAt E x).symm (chartAt E x x))
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x).symm (chartAt E x x) (v 0)) = c x (v 0)
  rw [(chartAt E x).left_inv (mem_chart_source E x)]
  exact congrArg (c x) (congrArg (fun a : E →L[ℝ] E => a (v 0)) hd')

theorem complexCovectorRawForm_bidegree (c : M → E →L[ℂ] ℂ) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 1 0 (complexCovectorRawForm c) := by
  apply (Analysis.DifferentialForms.Manifold.BidegreeInvariant.hasManifoldBidegree_iff_chartAt _).mpr
  intro x
  rw [complexCovectorRawForm_preferred]
  exact Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector_hasBidegree E (c x)

end

end OAI.RepresentationTheory.Theta.Geometric.Complex.CovectorPurity
