import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.MeasureTheory.Function.L2Space

/-! # Compact Kernel -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CompactKernel.CM.Construction

noncomputable section

/-! Compact operators obtained from norm-continuous families of scalar kernels. -/

open Set Filter _root_.Metric _root_.MeasureTheory
open scoped _root_.Topology BoundedContinuousFunction

variable {K H : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Evaluation against a bounded continuous family of linear functionals. -/
def compactKernelMap (k : K →ᵇ (H →L[ℂ] ℂ)) : H →L[ℂ] (K →ᵇ ℂ) :=
  LinearMap.mkContinuous
    { toFun u := (ContinuousLinearMap.apply ℂ ℂ u).compLeftContinuousBounded K k
      map_add' u v := by ext x; exact map_add (k x) u v
      map_smul' c u := by ext x; exact map_smul (k x) c u }
    ‖k‖ (by
      intro u
      change ‖(ContinuousLinearMap.apply ℂ ℂ u).compLeftContinuousBounded K k‖ ≤ ‖k‖ * ‖u‖
      apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg k) (norm_nonneg u))).mpr
      intro x
      change ‖k x u‖ ≤ ‖k‖ * ‖u‖
      exact ((k x).le_opNorm u).trans
        (mul_le_mul_of_nonneg_right (k.norm_coe_le_norm x) (norm_nonneg _)))

omit [CompactSpace K] in
@[simp]
theorem compactKernelMap_apply (k : K →ᵇ (H →L[ℂ] ℂ)) (u : H) (x : K) :
    compactKernelMap k u x = k x u := rfl

/-- A norm-continuous family over a compact parameter space gives a compact operator. -/
theorem compactKernelMap_isCompact (k : K →ᵇ (H →L[ℂ] ℂ)) :
    IsCompactOperator (compactKernelMap k) := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall
    (compactKernelMap k).toLinearMap (by norm_num : (0 : ℝ) < 1)).mpr
  let A : Set (K →ᵇ ℂ) := compactKernelMap k '' closedBall (0 : H) 1
  apply BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) ‖k‖)
    (isCompact_closedBall _ _) A
  · intro f x hf
    obtain ⟨u, hu, rfl⟩ := hf
    rw [mem_closedBall_zero_iff] at hu ⊢
    change ‖k x u‖ ≤ ‖k‖
    exact ((k x).le_opNorm u).trans
      ((mul_le_mul_of_nonneg_right (k.norm_coe_le_norm x) (norm_nonneg _)).trans
        (mul_le_of_le_one_right (norm_nonneg _) hu))
  · intro x
    apply Metric.equicontinuousAt_of_continuity_modulus (fun y => ‖k x - k y‖)
    · simpa only [Pi.sub_apply, sub_self, norm_zero] using
        ((continuous_const.sub k.continuous).norm.continuousAt.tendsto :
          Tendsto (fun y => ‖k x - k y‖) (𝓝 x) (𝓝 ‖k x - k x‖))
    · apply Filter.Eventually.of_forall
      intro y f
      obtain ⟨u, hu, heq⟩ := f.property
      have hnorm : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.mp hu
      change dist (f.val x) (f.val y) ≤ ‖k x - k y‖
      rw [← heq, compactKernelMap_apply, compactKernelMap_apply, dist_eq_norm]
      change ‖(k x - k y) u‖ ≤ ‖k x - k y‖
      exact ((k x - k y).le_opNorm u).trans
        (mul_le_of_le_one_right (norm_nonneg _) hnorm)

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- A continuous scalar kernel gives a norm-continuous family of L² functionals. -/
def continuousKernelFunctionals (k : C(K, C(X, ℂ))) :
    K →ᵇ (Lp ℂ 2 μ →L[ℂ] ℂ) :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun y => innerSL ℂ (ContinuousMap.toLp 2 μ ℂ (star (k y))),
      (innerSL ℂ).continuous.comp
        ((ContinuousMap.toLp 2 μ ℂ).continuous.comp k.continuous.star)⟩

/-- Integrating a continuous kernel against an L² function defines a bounded operator. -/
def continuousIntegralKernelMap (k : C(K, C(X, ℂ))) :
    Lp ℂ 2 μ →L[ℂ] (K →ᵇ ℂ) :=
  compactKernelMap (continuousKernelFunctionals μ k)

/-- The operator uses the literal integral of its kernel against the input. -/
theorem continuousIntegralKernelMap_apply (k : C(K, C(X, ℂ))) (u : Lp ℂ 2 μ) (y : K) :
    continuousIntegralKernelMap μ k u y = ∫ x, k y x * u x ∂μ := by
  change inner ℂ (ContinuousMap.toLp 2 μ ℂ (star (k y))) u = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) (μ := μ) (star (k y))] with x hx
  rw [hx, RCLike.inner_apply']
  simp

/-- Continuous integral kernels on compact parameter spaces define compact operators. -/
theorem continuousIntegralKernelMap_isCompact (k : C(K, C(X, ℂ))) :
    IsCompactOperator (continuousIntegralKernelMap μ k) :=
  compactKernelMap_isCompact (continuousKernelFunctionals μ k)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CompactKernel.CM.Construction
