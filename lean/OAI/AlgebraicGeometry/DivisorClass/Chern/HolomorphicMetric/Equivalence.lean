import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.IntegralPairZero
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.VariableMetricIntegral
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FormCompletion
import Mathlib.Analysis.Normed.Operator.Extend

/-! # Equivalence -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Equivalence

noncomputable section

/-! The identity on actual smooth forms extends between all metric completions and the original L² space. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem nonneg_le_sqrt_mul_of_sq_le {s t C : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hC : 0 ≤ C) (hb : s ^ 2 ≤ C * t ^ 2) : s ≤ Real.sqrt C * t := by
  apply (sq_le_sq₀ hs (mul_nonneg (Real.sqrt_nonneg C) ht)).mp
  rw [mul_pow, Real.sq_sqrt hC]
  exact hb

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
  (h k : Data.HolomorphicLineMetricData u) (n : ℕ)

theorem holomorphicFormL2WithInclusion_norm_bound :
    ∃ C : ℝ, ∀ a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n,
      ‖Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h n a‖ ≤ C * ‖Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V k n a‖ := by
  obtain ⟨C, hC, hb⟩ := h.formIntegralPair_uniform_bound V k
  refine ⟨Real.sqrt C, ?_⟩
  intro a
  exact nonneg_le_sqrt_mul_of_sq_le (norm_nonneg _) (norm_nonneg _) hC.le
    ((Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_norm_sq V h n a).trans_le ((hb n a).trans_eq
      (congrArg (fun r : ℝ => C * r) (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_norm_sq V k n a)).symm))

def holomorphicMetricL2Equiv : Holomorphic.IntegralPairZero.HolomorphicFormL2With V h n ≃L[ℂ] Holomorphic.IntegralPairZero.HolomorphicFormL2With V k n :=
  (LinearEquiv.refl ℂ (HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)).extend
    (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h n) (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V k n)
    (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_dense V h n) (holomorphicFormL2WithInclusion_norm_bound V k h n)
    (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_dense V k n) (holomorphicFormL2WithInclusion_norm_bound V h k n)

theorem holomorphicMetricL2Equiv_inclusion (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    holomorphicMetricL2Equiv V h k n (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h n a) =
      Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V k n a :=
  LinearEquiv.extend_eq _ _ _ _ _ _ _ a

theorem holomorphicMetricL2Equiv_symm_inclusion (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    (holomorphicMetricL2Equiv V h k n).symm (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V k n a) =
      Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h n a :=
  LinearEquiv.extend_symm_eq _ _ _ _ _ _ _ a

theorem holomorphicCanonicalL2Inclusion_norm (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    ‖Holomorphic.FormCompletion.holomorphicFormL2Inclusion V u n a‖ =
      ‖Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V (Data.holomorphicLineCanonicalMetric u) n a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Holomorphic.FormCompletion.holomorphicFormL2Inclusion_norm_sq, Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_norm_sq,
    Holomorphic.VariableMetricIntegral.holomorphicLineCanonicalMetric_formIntegralPair]

def holomorphicCanonicalL2Equiv :
    Holomorphic.IntegralPairZero.HolomorphicFormL2With V (Data.holomorphicLineCanonicalMetric u) n ≃ₗᵢ[ℂ] Holomorphic.FormCompletion.HolomorphicFormL2 V u n :=
  (LinearEquiv.refl ℂ (HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)).extendOfIsometry
    (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V (Data.holomorphicLineCanonicalMetric u) n) (Holomorphic.FormCompletion.holomorphicFormL2Inclusion V u n)
    (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_dense V (Data.holomorphicLineCanonicalMetric u) n)
    (Holomorphic.FormCompletion.holomorphicFormL2Inclusion_dense V u n) (holomorphicCanonicalL2Inclusion_norm V n)

theorem holomorphicCanonicalL2Equiv_inclusion (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    holomorphicCanonicalL2Equiv V n (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V (Data.holomorphicLineCanonicalMetric u) n a) =
      Holomorphic.FormCompletion.holomorphicFormL2Inclusion V u n a := by
  exact LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ a

def holomorphicMetricOriginalL2Equiv : Holomorphic.IntegralPairZero.HolomorphicFormL2With V h n ≃L[ℂ] Holomorphic.FormCompletion.HolomorphicFormL2 V u n :=
  (holomorphicMetricL2Equiv V h (Data.holomorphicLineCanonicalMetric u) n).trans
    (holomorphicCanonicalL2Equiv V n).toContinuousLinearEquiv

theorem holomorphicMetricOriginalL2Equiv_inclusion (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    holomorphicMetricOriginalL2Equiv V h n (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h n a) =
      Holomorphic.FormCompletion.holomorphicFormL2Inclusion V u n a := by
  change holomorphicCanonicalL2Equiv V n
    (holomorphicMetricL2Equiv V h (Data.holomorphicLineCanonicalMetric u) n (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h n a)) = _
  rw [holomorphicMetricL2Equiv_inclusion, holomorphicCanonicalL2Equiv_inclusion]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Equivalence
