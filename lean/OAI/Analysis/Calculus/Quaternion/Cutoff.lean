import OAI.Analysis.Calculus.Quaternion.Holomorphic
import OAI.Analysis.Calculus.Quaternion.CurrentOperations

/-! A real cutoff of a holomorphic phase has gradient in its normal row. -/

noncomputable section
namespace OAI.Analysis.Calculus.Quaternion

open OAI.Analysis.Calculus.Current
open scoped Matrix

theorem realCLM_complex_apply (L : ℂ →L[ℝ] ℝ) (z : ℂ) :
    L z = z.re * L 1 + z.im * L Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => arg 2; rw [hz]
  simp only [map_add, map_smul, smul_eq_mul]

theorem imaginaryGradient_real_comp_holomorphic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℂ) → ℂ} {g : ℂ → ℝ} {z : ι → ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℝ g (f z)) (a : ι) :
    imaginaryGradient (fun y => g (f y)) z a =
      OAI.Analysis.Calculus.Current.complexK (star (fderiv ℂ f z (Pi.single a 1))) *
        ((fderiv ℝ g (f z) 1) • OAI.Analysis.Calculus.Current.qi + (fderiv ℝ g (f z) Complex.I) • OAI.Analysis.Calculus.Current.qj) := by
  have hd : fderiv ℝ (fun y => g (f y)) z =
      (fderiv ℝ g (f z)).comp ((fderiv ℂ f z).restrictScalars ℝ) := by
    simpa only [Function.comp_def] using
      (hg.hasFDerivAt.comp z (hf.hasFDerivAt.restrictScalars ℝ)).fderiv
  simp only [imaginaryGradient, hd, ContinuousLinearMap.comp_apply]
  change (∑ α : Fin 3, (fderiv ℝ g (f z))
    ((fderiv ℂ f z) (imaginarySlot α • Pi.single a 1)) • threeSlots α) = _
  rw [Fin.sum_univ_three]
  change (fderiv ℝ g (f z)) ((fderiv ℂ f z) (0 • Pi.single a 1)) • (1 : Q) +
    (fderiv ℝ g (f z)) ((fderiv ℂ f z) (1 • Pi.single a 1)) • OAI.Analysis.Calculus.Current.qi +
    (fderiv ℝ g (f z)) ((fderiv ℂ f z) (Complex.I • Pi.single a 1)) • OAI.Analysis.Calculus.Current.qj = _
  simp only [zero_smul, one_smul, map_zero, map_smul, smul_eq_mul, zero_add]
  rw [realCLM_complex_apply _ (fderiv ℂ f z (Pi.single a 1)),
    realCLM_complex_apply _ (Complex.I * fderiv ℂ f z (Pi.single a 1))]
  ext <;> simp [OAI.Analysis.Calculus.Current.complexK, OAI.Analysis.Calculus.Current.qi, OAI.Analysis.Calculus.Current.qj] ; ring

theorem imaginaryGradient_real_comp_annihilates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℂ) → ℂ} {g : ℂ → ℝ} {z : ι → ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℝ g (f z))
    (A : Matrix ι ι Q)
    (htan : ∀ b, ∑ a, OAI.Analysis.Calculus.Current.complexK (fderiv ℂ f z (Pi.single a 1)) * A a b = 0) :
    star (imaginaryGradient (fun y => g (f y)) z) ᵥ* A = 0 := by
  funext b
  simp only [Matrix.vecMul, dotProduct, Pi.star_apply,
    imaginaryGradient_real_comp_holomorphic hf hg, star_mul]
  have hstar (a : ι) :
      star (OAI.Analysis.Calculus.Current.complexK (star (fderiv ℂ f z (Pi.single a 1)))) =
        OAI.Analysis.Calculus.Current.complexK (fderiv ℂ f z (Pi.single a 1)) := by
    ext <;> simp [OAI.Analysis.Calculus.Current.complexK]
  simp only [hstar, mul_assoc, ← Finset.mul_sum, htan, mul_zero, Pi.zero_apply]

end OAI.Analysis.Calculus.Quaternion
