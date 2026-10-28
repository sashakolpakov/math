import OAI.Analysis.HodgeTheory.Decomposition.LocalAdjoint
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Formal Adjoint Pair Derivative -/

namespace OAI.Analysis.HodgeTheory.Decomposition.FormalAdjointPairDerivative.Constructions

noncomputable section

/-! Testing the already constructed coordinate formal-adjoint numerator
amounts to differentiating its weighted scalar pairing. -/

variable {E F G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G] [Fintype ι]

theorem formalAdjointNumerator_pair_derivative (directions : ι → E) (symbol : ι → F →L[ℝ] G)
    (M : E → G →L[ℝ] G) (a : E → G) {x : E}
    (hM : DifferentiableAt ℝ M x) (ha : DifferentiableAt ℝ a x) (c : F) :
    inner ℝ (LocalAdjoint.Constructions.formalAdjointNumerator directions symbol M a x) c =
      -∑ i, fderiv ℝ (fun y => inner ℝ (M y (a y)) (symbol i c)) x (directions i) := by
  have hd (i : ι) :
      fderiv ℝ (fun y => inner ℝ (M y (a y)) (symbol i c)) x (directions i) =
        inner ℝ (fderiv ℝ (fun y => (symbol i).adjoint (M y (a y))) x (directions i)) c := by
    have hf := (symbol i).adjoint.differentiableAt.comp x (hM.clm_apply ha)
    have hh := hf.hasFDerivAt.inner ℝ (hasFDerivAt_const c x)
    have heq : (fun y => inner ℝ ((symbol i).adjoint (M y (a y))) c) =
        (fun y => inner ℝ (M y (a y)) (symbol i c)) := by
      funext y
      exact (symbol i).adjoint_inner_left _ _
    have h := congrArg (fun L : E →L[ℝ] ℝ => L (directions i)) hh.fderiv
    simp only [Function.comp_def] at h
    rw [heq] at h
    simpa only [add_apply, ContinuousLinearMap.comp_apply, zero_apply, inner_zero_right,
      zero_add, fderivInnerCLM_apply, ContinuousLinearMap.prod_apply] using h
  simp only [LocalAdjoint.Constructions.formalAdjointNumerator, inner_neg_left, sum_inner, hd]

end

end OAI.Analysis.HodgeTheory.Decomposition.FormalAdjointPairDerivative.Constructions
