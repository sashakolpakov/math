import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-! # Rapid Functions -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.RapidFunctions.LocalAnalysis

noncomputable section

section

/-! Continuous rapidly decreasing functions and their finite products.
These are the analytic estimates required for lattice periodization. -/

open scoped Classical NNReal

structure RapidFunction (V : Type*) [NormedAddCommGroup V] extends C(V, ℂ) where
  decay : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, (1 + ‖x‖) ^ k * ‖toContinuousMap x‖ ≤ C

instance {V : Type*} [NormedAddCommGroup V] : CoeFun (RapidFunction V) (fun _ => V → ℂ) :=
  ⟨fun f => f.toContinuousMap⟩

theorem RapidFunction.continuous {V : Type*} [NormedAddCommGroup V] (f : RapidFunction V) :
    Continuous f := f.toContinuousMap.continuous

def schwartzRapidFunction {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : SchwartzMap V ℂ) : RapidFunction V where
  toContinuousMap := f.toContinuousMap
  decay := Theta.PoissonAutomorphyNormalizationData.Construction.schwartz_one_add_bound f

variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]

theorem one_add_norm_pi_le_prod (x : ∀ i, V i) :
    1 + ‖x‖ ≤ ∏ i, (1 + ‖x i‖) := by
  have hp : (1 : ℝ) ≤ ∏ i, (1 + ‖x i‖) :=
    Finset.one_le_prod₀ (fun i _ => by linarith [norm_nonneg (x i)])
  have hx : ‖x‖ ≤ (∏ i, (1 + ‖x i‖)) - 1 := by
    apply (pi_norm_le_iff_of_nonneg (sub_nonneg.mpr hp)).mpr
    intro i
    have hiN : (1 : ℝ≥0) + ‖x i‖₊ ≤ ∏ j, (1 + ‖x j‖₊) :=
      Finset.single_le_prod (f := fun j => (1 : ℝ≥0) + ‖x j‖₊)
        (fun _ _ => le_add_of_nonneg_right zero_le) (Finset.mem_univ i)
    have hi : 1 + ‖x i‖ ≤ ∏ j, (1 + ‖x j‖) := by
      simpa only [NNReal.coe_add, NNReal.coe_one, NNReal.coe_prod, coe_nnnorm]
        using (NNReal.coe_le_coe.mpr hiN)
    linarith
  linarith

def piRapidFunction (f : ∀ i, RapidFunction (V i)) : RapidFunction (∀ i, V i) where
  toContinuousMap :=
    { toFun := fun x => ∏ i, f i (x i)
      continuous_toFun := continuous_finsetProd _ (fun i _ => (f i).continuous.comp (continuous_apply i)) }
  decay k := by
    choose C hC hb using fun i => (f i).decay k
    refine ⟨∏ i, C i, Finset.prod_nonneg (fun i _ => hC i), fun x => ?_⟩
    change (1 + ‖x‖) ^ k * ‖∏ i, f i (x i)‖ ≤ ∏ i, C i
    rw [norm_prod]
    calc
      _ ≤ (∏ i, (1 + ‖x i‖)) ^ k * ∏ i, ‖f i (x i)‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (one_add_norm_pi_le_prod x) k)
          (Finset.prod_nonneg (fun i _ => norm_nonneg _))
      _ = ∏ i, (1 + ‖x i‖) ^ k * ‖f i (x i)‖ := by
        rw [← Finset.prod_pow, Finset.prod_mul_distrib]
      _ ≤ _ := Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => hb i (x i))

end

section

/-! Locally uniform absolute convergence of lattice periodizations for
continuous rapidly decreasing functions. No differentiability is required. -/

open scoped Classical
open Filter _root_.TopologicalSpace Asymptotics

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

def shiftedRapidFunction (f : RapidFunction V) (a : V) : C(V, ℂ) :=
  ⟨fun x => f (x + a), f.continuous.comp (continuous_id.add continuous_const)⟩

theorem rapid_lattice_locally_summable_norm (L : Submodule ℤ V) [DiscreteTopology L]
    (f : RapidFunction V) (K : Compacts V) :
    Summable (fun a : L => ‖(shiftedRapidFunction f a.val).restrict K‖) := by
  let k := Module.finrank ℤ L + 1
  obtain ⟨C, hC, hf⟩ := f.decay k
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall 0
  let S := max 0 R
  have hS : 0 ≤ S := le_max_left _ _
  have hxS : ∀ x : K, ‖x.val‖ ≤ S := by
    intro x
    have h := hR x.property
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h.trans (le_max_right _ _)
  have hbound : ∀ (a : L), a ≠ 0 → ∀ x : K,
      ‖f (x.val + a.val)‖ ≤ (1 + S) ^ k * C * ‖a.val‖ ^ (-(k : ℝ)) := by
    intro a ha x
    have ha0 : 0 < ‖a.val‖ := norm_pos_iff.mpr (fun h => ha (Subtype.ext h))
    have htri : ‖a.val‖ ≤ ‖x.val + a.val‖ + ‖x.val‖ := by
      calc
        ‖a.val‖ = ‖(x.val + a.val) - x.val‖ := by congr 1; abel
        _ ≤ ‖x.val + a.val‖ + ‖x.val‖ := norm_sub_le _ _
    have hbase : ‖a.val‖ ≤ (1 + S) * (1 + ‖x.val + a.val‖) := by
      nlinarith [hxS x, norm_nonneg (x.val + a.val)]
    have hweight : ‖a.val‖ ^ k * ‖f (x.val + a.val)‖ ≤ (1 + S) ^ k * C := by
      calc
        _ ≤ ((1 + S) * (1 + ‖x.val + a.val‖)) ^ k * ‖f (x.val + a.val)‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hbase k) (norm_nonneg _)
        _ = (1 + S) ^ k * ((1 + ‖x.val + a.val‖) ^ k * ‖f (x.val + a.val)‖) := by
          rw [mul_pow, mul_assoc]
        _ ≤ (1 + S) ^ k * C := mul_le_mul_of_nonneg_left (hf _) (by positivity)
    rw [Real.rpow_neg ha0.le, Real.rpow_natCast, ← div_eq_mul_inv]
    exact (le_div_iff₀ (pow_pos ha0 k)).mpr (by simpa only [mul_comm] using hweight)
  have hr : -(k : ℝ) < -(Module.finrank ℤ L : ℝ) := by
    dsimp [k]
    push_cast
    linarith
  apply summable_of_isBigO (ZLattice.summable_norm_rpow L (-(k : ℝ)) hr)
  refine IsBigO.of_bound ((1 + S) ^ k * C) ?_
  filter_upwards [eventually_cofinite_ne (0 : L)] with a ha
  rw [norm_norm, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  exact hbound a ha

def rapidLatticePeriodization (L : Submodule ℤ V) [DiscreteTopology L]
    (f : RapidFunction V) : C(V, ℂ) := ∑' a : L, shiftedRapidFunction f a.val

theorem rapidLatticePeriodization_apply (L : Submodule ℤ V) [DiscreteTopology L]
    (f : RapidFunction V) (x : V) :
    rapidLatticePeriodization L f x = ∑' a : L, f (x + a.val) := by
  exact (ContinuousMap.tsum_apply (ContinuousMap.summable_of_locally_summable_norm
    (rapid_lattice_locally_summable_norm L f)) x).symm

theorem rapidLatticePeriodization_add (L : Submodule ℤ V) [DiscreteTopology L]
    (f : RapidFunction V) (a : L) (x : V) :
    rapidLatticePeriodization L f (x + a.val) = rapidLatticePeriodization L f x := by
  simp only [rapidLatticePeriodization_apply]
  have h := (Equiv.addLeft a).tsum_eq (fun b : L => f (x + b.val))
  simpa only [Equiv.coe_addLeft, Submodule.coe_add, add_assoc] using h

end

section

/-! Coordinate transport, Haar integrability, and absolute lattice
summability for continuous rapidly decreasing functions. -/

open scoped Classical
open _root_.MeasureTheory _root_.TopologicalSpace

variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

def RapidFunction.compLinearEquiv (f : RapidFunction E) (e : D ≃L[ℝ] E) : RapidFunction D where
  toContinuousMap := ⟨fun x => f (e x), f.continuous.comp e.continuous⟩
  decay k := by
    obtain ⟨C, hC, hf⟩ := f.decay k
    let M : ℝ := max 1 ‖e.symm.toContinuousLinearMap‖
    have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
    refine ⟨M ^ k * C, mul_nonneg (pow_nonneg hM _) hC, fun x => ?_⟩
    have he : ‖x‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e x‖ := by
      simpa only [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] using e.symm.toContinuousLinearMap.le_opNorm (e x)
    have hb : 1 + ‖x‖ ≤ M * (1 + ‖e x‖) := by
      have hm1 : 1 ≤ M := le_max_left _ _
      have hme : ‖e.symm.toContinuousLinearMap‖ ≤ M := le_max_right _ _
      nlinarith [norm_nonneg (e x)]
    change (1 + ‖x‖) ^ k * ‖f (e x)‖ ≤ M ^ k * C
    calc
      _ ≤ (M * (1 + ‖e x‖)) ^ k * ‖f (e x)‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hb k) (norm_nonneg _)
      _ = M ^ k * ((1 + ‖e x‖) ^ k * ‖f (e x)‖) := by rw [mul_pow, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hf _) (pow_nonneg hM _)

theorem RapidFunction.integrable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : RapidFunction E) (μ : Measure E) [μ.IsAddHaarMeasure] : Integrable (fun x => f x) μ := by
  let k := Module.finrank ℝ E + 1
  obtain ⟨C, hC, hf⟩ := f.decay k
  have hk : (Module.finrank ℝ E : ℝ) < (k : ℝ) := by dsimp [k]; norm_num
  have hi := (integrable_one_add_norm (μ := μ) hk).const_mul C
  apply hi.mono' f.continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv]
    exact (le_div_iff₀ (by positivity : 0 < (1 + ‖x‖) ^ k)).mpr
      (by simpa only [mul_comm] using hf x)

theorem rapid_lattice_summable_norm [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] (f : RapidFunction E) (x : E) :
    Summable (fun a : L => ‖f (x + a.val)‖) := by
  let K : Compacts E := ⟨{x}, isCompact_singleton⟩
  have hs := rapid_lattice_locally_summable_norm L f K
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
  intro a
  exact ((shiftedRapidFunction f a.val).restrict K).norm_coe_le_norm ⟨x, Set.mem_singleton x⟩

end

/-! Polynomially weighted integrability and rapid decay of translated
correlations. These estimates will control the corrected weak operators at
archimedean places. -/

open _root_.MeasureTheory

variable {V : Type*} [NormedAddCommGroup V]

def RapidFunction.weightedNorm (f : RapidFunction V) (k : ℕ) : RapidFunction V where
  toContinuousMap := ⟨fun x => ((1 + ‖x‖) ^ k * ‖f x‖ : ℝ), by
    exact Complex.continuous_ofReal.comp ((continuous_const.add continuous_norm).pow k |>.mul f.continuous.norm)⟩
  decay ℓ := by
    obtain ⟨C, hC, hf⟩ := f.decay (ℓ + k)
    refine ⟨C, hC, fun x => ?_⟩
    change (1 + ‖x‖) ^ ℓ * ‖(((1 + ‖x‖) ^ k * ‖f x‖ : ℝ) : ℂ)‖ ≤ C
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_assoc, ← pow_add]
    exact hf x

theorem RapidFunction.weighted_integrable [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (f : RapidFunction V) (μ : Measure V) [μ.IsAddHaarMeasure]
    (k : ℕ) : Integrable (fun x => (1 + ‖x‖) ^ k * ‖f x‖) μ :=
  ((f.weightedNorm k).integrable μ).re

theorem one_add_norm_le_translation_product (q x : V) :
    1 + ‖q‖ ≤ (1 + ‖x - q‖) * (1 + ‖x‖) := by
  have h : ‖q‖ ≤ ‖x‖ + ‖x - q‖ := by
    simpa only [sub_sub_cancel] using norm_sub_le x (x - q)
  nlinarith [norm_nonneg x, norm_nonneg (x - q)]

theorem rapid_translated_correlation_bound [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (f h : RapidFunction V)
    (μ : Measure V) [μ.IsAddHaarMeasure] (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : V) (phase : V → ℂ), (∀ x, ‖phase x‖ = 1) →
      (1 + ‖q‖) ^ k * ‖∫ x, phase x * f (x - q) * star (h x) ∂μ‖ ≤ C := by
  obtain ⟨C, hC, hf⟩ := f.decay k
  let I : ℝ := ∫ x, (1 + ‖x‖) ^ k * ‖h x‖ ∂μ
  have hI : 0 ≤ I := integral_nonneg (fun _ => by positivity)
  refine ⟨C * I, mul_nonneg hC hI, fun q phase hp => ?_⟩
  have hb (x : V) : (1 + ‖q‖) ^ k * ‖phase x * f (x - q) * star (h x)‖ ≤
      C * ((1 + ‖x‖) ^ k * ‖h x‖) := by
    rw [norm_mul, norm_mul, hp, one_mul, norm_star]
    have hx := one_add_norm_le_translation_product q x
    calc
      _ ≤ ((1 + ‖x - q‖) * (1 + ‖x‖)) ^ k * (‖f (x - q)‖ * ‖h x‖) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hx k) (by positivity)
      _ = ((1 + ‖x - q‖) ^ k * ‖f (x - q)‖) * ((1 + ‖x‖) ^ k * ‖h x‖) := by
        rw [mul_pow]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hf (x - q)) (by positivity)
  calc
    _ ≤ (1 + ‖q‖) ^ k * ∫ x, ‖phase x * f (x - q) * star (h x)‖ ∂μ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = ∫ x, (1 + ‖q‖) ^ k * ‖phase x * f (x - q) * star (h x)‖ ∂μ :=
      (integral_const_mul _ _).symm
    _ ≤ ∫ x, C * ((1 + ‖x‖) ^ k * ‖h x‖) ∂μ :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity)
        ((h.weighted_integrable μ k).const_mul C) (Filter.Eventually.of_forall hb)
    _ = _ := integral_const_mul _ _

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.RapidFunctions.LocalAnalysis
