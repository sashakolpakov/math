import OAI.Analysis.Calculus.FiniteExtension.Halfspace.Extension.Moments

/-! Normal dilations of a general complemented coordinate halfspace. -/

noncomputable section
open Set
namespace OAI.Analysis.Calculus.FiniteExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def reflectionLinear (ℓ : E →L[ℝ] ℝ) (ν : E) (a : ℝ) : E →L[ℝ] E :=
  (ContinuousLinearMap.id ℝ E - ℓ.smulRight ν) + a • ℓ.smulRight ν

theorem reflectionLinear_apply (ℓ : E →L[ℝ] ℝ) (ν : E) (a : ℝ) (x : E) :
    reflectionLinear ℓ ν a x = x - ℓ x • ν + a • (ℓ x • ν) := rfl

theorem reflectionLinear_normal (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1)
    (a : ℝ) (x : E) : ℓ (reflectionLinear ℓ ν a x) = a * ℓ x := by
  simp only [reflectionLinear_apply, map_add, map_sub, map_smul, hν, smul_eq_mul, mul_one]
  ring

theorem reflectionLinear_boundary (ℓ : E →L[ℝ] ℝ) (ν : E) (a : ℝ)
    {x : E} (hx : ℓ x = 0) : reflectionLinear ℓ ν a x = x := by
  simp only [reflectionLinear_apply, hx, zero_smul, sub_zero, smul_zero, add_zero]

theorem reflectionLinear_maps_negative (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1)
    {a : ℝ} (ha : a ≤ 0) :
    MapsTo (reflectionLinear ℓ ν a) {x | ℓ x ≤ 0} {x | 0 ≤ ℓ x} := by
  intro x hx
  change 0 ≤ ℓ (reflectionLinear ℓ ν a x)
  rw [reflectionLinear_normal ℓ ν hν]
  exact mul_nonneg_of_nonpos_of_nonpos ha hx

theorem reflectionLinear_jet_moments {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {N q : ℕ} (hq : q < N) (ℓ : E →L[ℝ] ℝ) (ν : E)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) F) :
    (∑ j : Fin N, OAI.Analysis.Normed.Function.Sobolev.reflectionCoefficient N j •
      A.compContinuousLinearMap (fun _ => reflectionLinear ℓ ν (OAI.Analysis.Normed.Function.Sobolev.reflectionNode j))) = A :=
  reflection_continuousMultilinear_moments hq A _ _ (sub_add_cancel _ _)

end OAI.Analysis.Calculus.FiniteExtension
