import OAI.Analysis.HodgeTheory.Decomposition.FreezingError
import OAI.Analysis.HodgeTheory.Decomposition.GradientEnergy

/-! # Integrated Freezing -/

namespace OAI.Analysis.HodgeTheory.Decomposition.IntegratedFreezing.Constructions

noncomputable section

/-! Integrated coefficient-freezing error for genuine vector-valued
Schwartz functions, with hypotheses only on the input support. -/

open _root_.MeasureTheory LineDeriv
open scoped SchwartzMap BigOperators

theorem norm_sq_le_twice_add_error {G : Type*} [NormedAddCommGroup G] (v w : G) :
    ‖w‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 + 2 * ‖v - w‖ ^ 2 := by
  have h : ‖w‖ ≤ ‖v‖ + ‖v - w‖ := by
    simpa only [sub_sub_cancel] using norm_sub_le v (v - w)
  have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  nlinarith [sq_nonneg (‖v‖ - ‖v - w‖)]

variable {E F G ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [Fintype ι]

theorem integrated_firstOrder_freezing
    (C : ι → E → F →L[ℝ] G) (Z : E → F →L[ℝ] G) (directions : ι → E)
    (a : 𝓢(E, F)) (v w : 𝓢(E, G)) (z : E) (ε M : ℝ) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hv : ∀ x, v x = (∑ i, C i x (fderiv ℝ (a : E → F) x (directions i))) + Z x (a x))
    (hw : ∀ x, w x = ∑ i, C i z (fderiv ℝ (a : E → F) x (directions i)))
    (hC : ∀ x ∈ tsupport a, ∀ i, ‖C i x - C i z‖ ≤ ε)
    (hZ : ∀ x ∈ tsupport a, ‖Z x‖ ≤ M) :
    (∫ x, ‖w x‖ ^ 2) ≤ 2 * (∫ x, ‖v x‖ ^ 2) +
      4 * ε ^ 2 * Fintype.card ι * (∑ i, ∫ x, ‖∂_{directions i} a x‖ ^ 2) +
      4 * M ^ 2 * ∫ x, ‖a x‖ ^ 2 := by
  have hpoint (x : E) : ‖w x‖ ^ 2 ≤ 2 * ‖v x‖ ^ 2 +
      4 * ε ^ 2 * Fintype.card ι * (∑ i, ‖∂_{directions i} a x‖ ^ 2) + 4 * M ^ 2 * ‖a x‖ ^ 2 := by
    by_cases hx : x ∈ tsupport a
    · have he := FreezingError.Constructions.firstOrder_freezing_error_sq C Z directions (a : E → F) x z ε M hε hM (hC x hx) (hZ x hx)
      rw [← hv x, ← hw x] at he
      simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
      nlinarith [norm_sq_le_twice_add_error (v x) (w x)]
    · have hd := fderiv_of_notMem_tsupport ℝ hx
      have ha := image_eq_zero_of_notMem_tsupport hx
      rw [hv, hw]
      simp only [hd, ha, zero_apply, map_zero, Finset.sum_const_zero, add_zero, norm_zero,
        zero_pow (by norm_num : 2 ≠ 0), mul_zero, SchwartzMap.lineDerivOp_apply_eq_fderiv, le_refl]
  have hG : Integrable (fun x => ∑ i, ‖∂_{directions i} a x‖ ^ 2) volume :=
    integrable_finsetSum _ (fun i _ => GradientEnergy.Constructions.schwartz_normsq_integrable (∂_{directions i} a))
  have h := integral_mono (GradientEnergy.Constructions.schwartz_normsq_integrable w)
    (((GradientEnergy.Constructions.schwartz_normsq_integrable v).const_mul 2).add
      (hG.const_mul (4 * ε ^ 2 * Fintype.card ι)) |>.add
      ((GradientEnergy.Constructions.schwartz_normsq_integrable a).const_mul (4 * M ^ 2))) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add, integral_add, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun i _ => GradientEnergy.Constructions.schwartz_normsq_integrable (∂_{directions i} a))] at h
  · exact h
  · exact (GradientEnergy.Constructions.schwartz_normsq_integrable v).const_mul 2
  · exact hG.const_mul _
  · exact ((GradientEnergy.Constructions.schwartz_normsq_integrable v).const_mul 2).add (hG.const_mul _)
  · exact (GradientEnergy.Constructions.schwartz_normsq_integrable a).const_mul _

end

end OAI.Analysis.HodgeTheory.Decomposition.IntegratedFreezing.Constructions
