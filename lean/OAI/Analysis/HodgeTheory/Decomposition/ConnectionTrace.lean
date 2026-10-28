import OAI.Analysis.HodgeTheory.Decomposition.CovectorConnection
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Connection Trace -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ConnectionTrace.Constructions

noncomputable section

/-! The trace covector of a symmetric connection and the cancellation of
its alternated action on covectors. -/

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [DecidableEq ι]

theorem symmetricConnection_trace_covector (b : Module.Basis ι ℝ E)
    (Γ : E →L[ℝ] E →L[ℝ] E) (hΓ : ∀ u v, Γ u v = Γ v u) :
    (∑ i, (LinearMap.toMatrix b b (Γ (b i)).toLinearMap).trace • (b.coord i).toContinuousLinearMap) =
      ∑ i, (b.coord i).toContinuousLinearMap.comp (Γ (b i)) := by
  let τ := ∑ i, (b.coord i).toContinuousLinearMap.comp (Γ (b i))
  have ht (i : ι) : τ (b i) = (LinearMap.toMatrix b b (Γ (b i)).toLinearMap).trace := by
    simp only [τ, sum_apply, ContinuousLinearMap.comp_apply, Matrix.trace, Matrix.diag_apply,
      LinearMap.toMatrix_apply]
    apply Finset.sum_congr rfl
    intro j _
    change b.repr (Γ (b j) (b i)) j = b.repr (Γ (b i) (b j)) j
    rw [hΓ]
  calc
    _ = ∑ i, τ (b i) • (b.coord i).toContinuousLinearMap := by simp only [ht]
    _ = τ := by
      ext v
      simp only [sum_apply, smul_apply, smul_eq_mul]
      change (∑ i, τ (b i) * b.repr v i) = τ v
      have h := congrArg τ (b.sum_repr v)
      simp only [map_sum, map_smul, smul_eq_mul] at h
      simpa only [mul_comm] using h

omit [DecidableEq ι] in
theorem symmetricConnection_alternated_action (b : Module.Basis ι ℝ E) (n : ℕ)
    (Γ : E →L[ℝ] E →L[ℝ] E) (hΓ : ∀ u v, Γ u v = Γ v u) (a : DifferentialForms.Manifold.Basic.FormValue E n) :
    (∑ i, SymbolDifferential.Constructions.exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap
      (CovectorConnection.Constructions.covectorInfinitesimalAction n (Γ (b i)) a)) = 0 := by
  let L := (a.fderivCompContinuousLinearMap (ContinuousLinearMap.id ℝ E)).comp Γ
  have hexp := congrArg (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ)
    (SymbolDifferential.Constructions.derivative_basis_expansion b n L)
  rw [map_sum] at hexp
  have hz := ContinuousAlternatingMap.alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero
    a (ContinuousLinearMap.id ℝ E) hΓ
  exact hexp.symm.trans hz

end

end OAI.Analysis.HodgeTheory.Decomposition.ConnectionTrace.Constructions
