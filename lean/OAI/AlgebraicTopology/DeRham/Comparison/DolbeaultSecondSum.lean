import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldDolbeault

/-! # Dolbeault Second Sum -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.DolbeaultSecondSum.PureManifoldForm

/-!
The four second Dolbeault derivatives sum to zero. This is obtained directly
from the genuine exterior differential squared and the two first-derivative
decompositions. All four terms are transported to the same actual degree.
No independence of bidegrees is assumed in this algebraic step.
-/

open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {p q : ℕ}

/-- The four second derivatives, in their common degree, sum to zero by `d²=0`. -/
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.second_derivative_sum (form : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q) :
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree (by omega : ((p + 1) + 1) + q = p + q + 2)
        (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime form)).1 +
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree (by omega : (p + 1) + (q + 1) = p + q + 2)
        (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime form)).1) +
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree (by omega : (p + 1) + (q + 1) = p + q + 2)
        (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime form)).1 +
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree (by omega : p + ((q + 1) + 1) = p + q + 2)
        (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime form)).1) = 0 := by
  have hfirst := congrArg
    (fun s : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (p + q + 1) =>
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree (by omega : (p + q + 1) + 1 = p + q + 2)
        (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d s))
    (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime_add_dDoublePrime form)
  simp only [map_add, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_castDegree,
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_add, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_castDegree,
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_squared, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_zero] at hfirst
  have hprime := congrArg
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree (by omega : ((p + 1) + q) + 1 = p + q + 2))
    (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime_add_dDoublePrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime form))
  simp only [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_add,
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_castDegree] at hprime
  have hdoublePrime := congrArg
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree (by omega : (p + (q + 1)) + 1 = p + q + 2))
    (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime_add_dDoublePrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime form))
  simp only [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_add,
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_castDegree] at hdoublePrime
  rw [hprime, hdoublePrime]
  exact hfirst

end OAI.AlgebraicTopology.DeRham.Comparison.DolbeaultSecondSum.PureManifoldForm
