import OAI.RepresentationTheory.Theta.Definitions
import OAI.AlgebraicGeometry.ComplexMultiplication.SparseLatticeSums

/-! # Sparse -/

namespace OAI.Analysis.Theta.Sparse.GaussianConvergenceConstruction

noncomputable section

open scoped Classical BigOperators _root_.Topology BoundedContinuousFunction
open Filter Set _root_.Metric OAI.AlgebraicGeometry.ComplexMultiplication.SparseLatticeSums.CM

lemma sparse_uniform_of_summable_bound
    {V W P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    [TopologicalSpace P]
    (L : Submodule ℤ V) [DiscreteTopology L]
    (K : Set P) (f : L → P → W)
    (hf : ∀ x, ContinuousOn (f x) K)
    (M : L → ℝ) (hM0 : ∀ x, 0 ≤ M x) (hM : Summable M)
    (hb : ∀ x p, p ∈ K → ‖f x p‖ ≤ M x) (a : L) :
    TendstoUniformlyOn
      (fun n p => AlgebraicGeometry.ComplexMultiplication.SparseLatticeSums.CM.sparseLatticeSum L (fun x => f x p) a n)
      (f a) atTop K := by
  let F : L → (K →ᵇ W) := fun x =>
    BoundedContinuousFunction.ofNormedAddCommGroup (fun p => f x p)
      (continuousOn_iff_continuous_domRestrict.mp (hf x)) (M x) (fun p => hb x p p.property)
  have hFbound (x : L) : ‖F x‖ ≤ M x :=
    (BoundedContinuousFunction.norm_le (hM0 x)).mpr (fun p => hb x p p.property)
  have hF : Summable (fun x => ‖F x‖) :=
    hM.of_nonneg_of_le (fun _ => norm_nonneg _) hFbound
  have hSn (n : ℕ) : Summable (fun x : L =>
      if AlgebraicGeometry.ComplexMultiplication.SparseLatticeSums.CM.SparseLatticeCoset L n a x then F x else 0) := by
    apply Summable.of_norm_bounded hM
    intro x
    split_ifs
    · exact hFbound x
    · simpa using hM0 x
  have heval (n : ℕ) (p : K) :
      (AlgebraicGeometry.ComplexMultiplication.SparseLatticeSums.CM.sparseLatticeSum L F a n) p = AlgebraicGeometry.ComplexMultiplication.SparseLatticeSums.CM.sparseLatticeSum L (fun x => f x p) a n := by
    change (BoundedContinuousFunction.evalCLM ℂ p)
      (∑' x : L, if AlgebraicGeometry.ComplexMultiplication.SparseLatticeSums.CM.SparseLatticeCoset L n a x then F x else 0) = _
    rw [(BoundedContinuousFunction.evalCLM ℂ p).map_tsum (hSn n)]
    apply tsum_congr
    intro x
    split_ifs <;> rfl
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  have h := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    (AlgebraicGeometry.ComplexMultiplication.SparseLatticeSums.CM.sparseLatticeSum_tendsto L F hF a)
  change TendstoUniformly (fun n (p : K) => (AlgebraicGeometry.ComplexMultiplication.SparseLatticeSums.CM.sparseLatticeSum L F a n) p)
    (fun p : K => f a p) atTop at h
  simpa only [heval, Function.comp_apply] using! h

end

end OAI.Analysis.Theta.Sparse.GaussianConvergenceConstruction
