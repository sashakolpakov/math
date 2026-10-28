import OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.DerivationDefect
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # Automorphism Transversal -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.AutomorphismTransversal.Construction

noncomputable section

/-! In a complement to the derivations, the identity is an isolated
bracket-preserving map. The proof bounds the quadratic remainder by the
injective linearized equations. -/

open scoped Classical

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]
  [FiniteDimensional ℝ L]

def finiteContinuousBilinear (B : L →ₗ[ℝ] L →ₗ[ℝ] L) : L →L[ℝ] L →L[ℝ] L :=
  ((LinearMap.toContinuousLinearMap : (L →ₗ[ℝ] L) ≃ₗ[ℝ] (L →L[ℝ] L)).toLinearMap.comp
    B).toContinuousLinearMap

theorem finiteContinuousBilinear_apply (B : L →ₗ[ℝ] L →ₗ[ℝ] L) (x y : L) :
    finiteContinuousBilinear B x y = B x y := rfl

def continuousBilinearDerivationDefect (B : L →L[ℝ] L →L[ℝ] L) :
    (L →L[ℝ] L) →L[ℝ] (L →L[ℝ] L →L[ℝ] L) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => (ContinuousLinearMap.compL ℝ L L L T).comp B -
        B.comp T - (B.flip.comp T).flip
      map_add' := fun T S => by
        ext x y
        change (T + S) (B x y) - B ((T + S) x) y - B x ((T + S) y) =
          (T (B x y) - B (T x) y - B x (T y)) +
          (S (B x y) - B (S x) y - B x (S y))
        simp only [add_apply, map_add]
        abel
      map_smul' := fun c T => by
        ext x y
        change (c • T) (B x y) - B ((c • T) x) y - B x ((c • T) y) =
          c • (T (B x y) - B (T x) y - B x (T y))
        simp only [smul_apply, map_smul, smul_sub] }

theorem continuousBilinearDerivationDefect_apply (B : L →L[ℝ] L →L[ℝ] L)
    (T : L →L[ℝ] L) (x y : L) :
    continuousBilinearDerivationDefect B T x y =
      T (B x y) - B (T x) y - B x (T y) := rfl

theorem continuousBilinearDerivationDefect_of_preserving
    (B : L →L[ℝ] L →L[ℝ] L) (T : L →L[ℝ] L)
    (hT : ∀ x y, (ContinuousLinearMap.id ℝ L + T) (B x y) =
      B ((ContinuousLinearMap.id ℝ L + T) x) ((ContinuousLinearMap.id ℝ L + T) y))
    (x y : L) : continuousBilinearDerivationDefect B T x y = B (T x) (T y) := by
  have he := hT x y
  simp only [add_apply, ContinuousLinearMap.id_apply, map_add] at he
  rw [continuousBilinearDerivationDefect_apply]
  apply sub_eq_zero.mp
  calc
    _ = (B x y + T (B x y)) -
      (B x y + B (T x) y + (B x (T y) + B (T x) (T y))) := by abel
    _ = 0 := sub_eq_zero.mpr he

theorem continuousBilinearDerivationDefect_norm_bound
    (B : L →L[ℝ] L →L[ℝ] L) (T : L →L[ℝ] L)
    (hT : ∀ x y, (ContinuousLinearMap.id ℝ L + T) (B x y) =
      B ((ContinuousLinearMap.id ℝ L + T) x) ((ContinuousLinearMap.id ℝ L + T) y)) :
    ‖continuousBilinearDerivationDefect B T‖ ≤ ‖B‖ * ‖T‖ ^ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound₂ (continuousBilinearDerivationDefect B T)
    (C := ‖B‖ * ‖T‖ ^ 2) (by positivity) ?_
  intro x y
  rw [continuousBilinearDerivationDefect_of_preserving B T hT]
  calc
    ‖B (T x) (T y)‖ ≤ ‖B‖ * ‖T x‖ * ‖T y‖ :=
      ContinuousLinearMap.le_opNorm₂ _ _ _
    _ ≤ ‖B‖ * (‖T‖ * ‖x‖) * (‖T‖ * ‖y‖) := by
      gcongr
      · exact T.le_opNorm x
      · exact T.le_opNorm y
    _ = _ := by ring

theorem linear_complement_norm_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : E →ₗ[ℝ] F) (W : Submodule ℝ E) (hW : Disjoint W (LinearMap.ker D)) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : E, x ∈ W → ‖x‖ ≤ K * ‖D x‖ := by
  have hD : LinearMap.ker (D.domRestrict W) = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    apply (injective_iff_map_eq_zero (D.domRestrict W)).mpr
    intro T hT
    apply Subtype.ext
    exact (Submodule.disjoint_def.mp hW T.val T.property hT)
  obtain ⟨K, hK, hbound⟩ := (D.domRestrict W).exists_antilipschitzWith hD
  refine ⟨K, hK, fun x hx => ?_⟩
  exact ZeroHomClass.bound_of_antilipschitz (D.domRestrict W) hbound ⟨x, hx⟩

theorem quadratic_remainder_isolated_on_complement
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : E →ₗ[ℝ] F) (W : Submodule ℝ E) (hW : Disjoint W (LinearMap.ker D))
    (b : ℝ) (hb : 0 ≤ b) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : E, x ∈ W → ‖x‖ < ε → ‖D x‖ ≤ b * ‖x‖ ^ 2 → x = 0 := by
  obtain ⟨K, hK, hbound⟩ := linear_complement_norm_bound D W hW
  let C : ℝ := K * b
  have hC : 0 ≤ C := mul_nonneg hK.le hb
  refine ⟨(C + 1)⁻¹, inv_pos.mpr (by positivity), ?_⟩
  intro x hxW hsmall hupper
  have hquad : ‖x‖ ≤ C * ‖x‖ ^ 2 := by
    calc
      ‖x‖ ≤ K * ‖D x‖ := hbound x hxW
      _ ≤ K * (b * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_left hupper hK.le
      _ = _ := by dsimp [C]; ring
  apply norm_eq_zero.mp
  have hprod : ‖x‖ * (C + 1) < 1 := by
    have ht := mul_lt_mul_of_pos_right hsmall (by positivity : 0 < C + 1)
    simpa only [inv_mul_cancel₀ (by positivity : C + 1 ≠ 0)] using ht
  nlinarith [norm_nonneg x, mul_nonneg hC (norm_nonneg x)]

theorem bilinear_stabilizer_transversal_isolated
    (B : L →L[ℝ] L →L[ℝ] L)
    (W : Submodule ℝ (L →L[ℝ] L))
    (hW : Disjoint W (LinearMap.ker (continuousBilinearDerivationDefect B).toLinearMap)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ T : L →L[ℝ] L, T ∈ W → ‖T‖ < ε →
      (∀ x y, (ContinuousLinearMap.id ℝ L + T) (B x y) =
        B ((ContinuousLinearMap.id ℝ L + T) x) ((ContinuousLinearMap.id ℝ L + T) y)) → T = 0 := by
  let : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
  let : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
  let : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance
  let : NormedAddCommGroup (L →L[ℝ] L →L[ℝ] L) := inferInstance
  let : NormedSpace ℝ (L →L[ℝ] L →L[ℝ] L) := inferInstance
  obtain ⟨ε, hε, h⟩ := quadratic_remainder_isolated_on_complement
    (E := L →L[ℝ] L) (F := L →L[ℝ] L →L[ℝ] L)
    (continuousBilinearDerivationDefect B).toLinearMap W hW ‖B‖ (norm_nonneg B)
  exact ⟨ε, hε, fun T hTW hsmall hT => h T hTW hsmall
    (continuousBilinearDerivationDefect_norm_bound B T hT)⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.AutomorphismTransversal.Construction
