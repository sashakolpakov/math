import OAI.AlgebraicGeometry.ComplexMultiplication.EmbeddingCoefficientField

/-! # Scalar Descent Of -/

namespace OAI.Algebra.FieldTheory.ScalarDescentOf

noncomputable section

/-!
# ScalarDescent: scalar-trace descent, conditional on TracePairing

The hypothesis `hTracePairing` is the supplied TracePairing proposition specialized to the
finite Galois coefficient extension `K / ℚ`. It constructs the trace-dual
basis used for reconstruction; no statement stub is imported or invoked.
The rational space `V` represents tensors or maps, and `Hpq` is the prescribed
complex Hodge subspace. No stability of all of `Hpq`, finite-dimensionality
of `V`, or additional substantive input is needed.
-/

open scoped TensorProduct
open OAI.AlgebraicGeometry.ComplexMultiplication.EmbeddingCoefficientField.CM

/-- Reconstruct a tensor using the dual basis provided by TracePairing. -/
theorem trace_reconstruction_of_TracePairing
    (K V : Type*) [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [AddCommGroup V] [Module ℚ V]
    (hTracePairing : (Algebra.traceForm ℚ K).Nondegenerate)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℚ K) (t : K ⊗[ℚ] V) :
    ∑ i, ((Algebra.traceForm ℚ K).dualBasis hTracePairing b) i ⊗ₜ[ℚ]
      AlgebraicGeometry.ComplexMultiplication.ScalarDescent.CM.scalarTrace ℚ K V (b i • t) = t := by
  induction t using TensorProduct.inductionOn with
  | tmul a v =>
    simp only [TensorProduct.smul_tmul', smul_eq_mul, AlgebraicGeometry.ComplexMultiplication.ScalarDescent.CM.scalarTrace_tmul]
    calc
      ∑ i, ((Algebra.traceForm ℚ K).dualBasis hTracePairing b) i ⊗ₜ[ℚ]
          (Algebra.trace ℚ K (b i * a) • v) =
          (∑ i, ((Algebra.traceForm ℚ K).dualBasis hTracePairing b).repr a i •
            ((Algebra.traceForm ℚ K).dualBasis hTracePairing b) i) ⊗ₜ[ℚ] v := by
        rw [TensorProduct.sum_tmul]
        apply Finset.sum_congr rfl
        intro i _
        rw [(Algebra.traceForm ℚ K).dualBasis_repr_apply,
          Algebra.traceForm_apply, mul_comm a (b i), TensorProduct.smul_tmul]
      _ = a ⊗ₜ[ℚ] v := by rw [Module.Basis.sum_repr]
  | add x y hx hy =>
    simp only [smul_add, map_add, TensorProduct.tmul_add,
      Finset.sum_add_distrib, hx, hy]

/-- ScalarDescent, with the supplied trace-pairing nondegeneracy as an explicit input. -/
theorem scalar_trace_descent
    (K : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (V : Type*) [AddCommGroup V] [Module ℚ V]
    (Hpq : Submodule ℂ (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification V))
    (t : K ⊗[ℚ] V)
    (hconj : ∀ σ : K ≃ₐ[ℚ] K,
      AlgebraicGeometry.ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K V (AlgebraicGeometry.ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K V σ t) ∈ Hpq)
    (hTracePairing : (Algebra.traceForm ℚ K).Nondegenerate) :
    t ∈ Submodule.span K
      {y : K ⊗[ℚ] V |
        ∃ v : V,
          y = (1 : K) ⊗ₜ[ℚ] v ∧
          (1 : ℂ) ⊗ₜ[ℚ] v ∈ Hpq} := by
  classical
  have htrace (a : K) :
      (1 : ℂ) ⊗ₜ[ℚ] AlgebraicGeometry.ComplexMultiplication.ScalarDescent.CM.scalarTrace ℚ K V (a • t) ∈ Hpq := by
    change AlgebraicGeometry.ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K V
      ((1 : K) ⊗ₜ[ℚ] AlgebraicGeometry.ComplexMultiplication.ScalarDescent.CM.scalarTrace ℚ K V (a • t)) ∈ Hpq
    rw [AlgebraicGeometry.ComplexMultiplication.ScalarDescent.CM.scalarTrace_eq_sum_conjugates, map_sum]
    apply Hpq.sum_mem
    intro σ _
    rw [AlgebraicGeometry.ComplexMultiplication.ScalarDescent.CM.scalarConjugate_smul, AlgebraicGeometry.ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion_smul]
    exact Hpq.smul_mem _ (hconj σ)
  let b := Module.finBasis ℚ K
  rw [← trace_reconstruction_of_TracePairing K V hTracePairing b t]
  apply Submodule.sum_mem
  intro i _
  have hmem : (1 : K) ⊗ₜ[ℚ] AlgebraicGeometry.ComplexMultiplication.ScalarDescent.CM.scalarTrace ℚ K V (b i • t) ∈
      Submodule.span K
        {y : K ⊗[ℚ] V |
          ∃ v : V, y = (1 : K) ⊗ₜ[ℚ] v ∧ (1 : ℂ) ⊗ₜ[ℚ] v ∈ Hpq} :=
    Submodule.subset_span ⟨_, rfl, htrace (b i)⟩
  simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
    Submodule.smul_mem _ (((Algebra.traceForm ℚ K).dualBasis hTracePairing b) i) hmem

end

end OAI.Algebra.FieldTheory.ScalarDescentOf
