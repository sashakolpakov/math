import OAI.Analysis.PDE.Dirichlet.CoordinateTransport
import OAI.Analysis.PDE.Dirichlet.RealOperator

/-! The real coordinate matrix represents exactly the same elliptic operator. -/

noncomputable section
open Set InnerProductSpace
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Elliptic

theorem trace_comp_eq_coordinate_contraction
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] (b : OrthonormalBasis ι ℝ E) (A G : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) :
    LinearMap.trace ℝ E (A.comp G).toLinearMap =
      ∑ i, ∑ j, inner ℝ (A (b i)) (b j) * inner ℝ (G (b i)) (b j) := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℝ (b i) (A (G (b i))) = _
  have hs : inner ℝ (A (b i)) (G (b i)) = inner ℝ (b i) (A (G (b i))) :=
    hA (b i) (G (b i))
  rw [← hs]
  have hh := b.sum_inner_mul_inner (A (b i)) (G (b i))
  simpa only [real_inner_comm (b _) (G (b i))] using hh.symm

theorem ellipticTrace_eq_indexedNondivergenceOperator {n s : ℕ}
    (A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)
    (u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) (hu : ContDiff ℝ 2 u) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)
    (hA : (A x).toLinearMap.IsSymmetric) :
    OAI.Analysis.PDE.Elliptic.ellipticTrace A u x = OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator
      (fun y => OAI.Analysis.PDE.Dirichlet.operatorCoordinateMatrix (A y)) u x := by
  rw [OAI.Analysis.PDE.Elliptic.ellipticTrace, trace_comp_eq_coordinate_contraction (EuclideanSpace.basisFun _ _) _ _ hA]
  unfold OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [EuclideanSpace.basisFun_apply]
  change inner ℝ (A x (OAI.Analysis.PDE.Dirichlet.coordinateVector i)) (OAI.Analysis.PDE.Dirichlet.coordinateVector j) *
    inner ℝ (fderiv ℝ (gradient u) x (OAI.Analysis.PDE.Dirichlet.coordinateVector i)) (OAI.Analysis.PDE.Dirichlet.coordinateVector j) = _
  rw [OAI.Analysis.PDE.Elliptic.inner_fderiv_gradient hu]
  rfl

end OAI.Analysis.PDE.Nonlinear
