import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.MeanValue

/-! # Parametric Inverse -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.ParametricInverse.Abelian

noncomputable section

/-!
A uniform inverse construction for maps with a continuous parameter.
Only their vertical variables need linear approximation estimates. The
inverse exists on a common ball and is jointly continuous by a uniform
distance estimate; parameter differentiability is not required.
-/

open Set _root_.Metric Filter
open scoped _root_.Topology NNReal

variable {P V : Type} [TopologicalSpace P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [TopologicalSpace P] [CompleteSpace V] in
theorem approximates_id_inverse_bound
    (f : V → V) (D : Set V)
    (hf : ApproximatesLinearOn f (ContinuousLinearMap.id ℝ V) D (1 / 2))
    (x : V) (hx : x ∈ D) (y : V) (hy : y ∈ D) :
    ‖x - y‖ ≤ 2 * ‖f x - f y‖ := by
  have he := hf x hx y hy
  change ‖f x - f y - (x - y)‖ ≤ (1 / 2 : ℝ) * ‖x - y‖ at he
  have hnorm := norm_sub_le (f x - f y) (f x - f y - (x - y))
  have hid : f x - f y - (f x - f y - (x - y)) = x - y := by abel
  rw [hid] at hnorm
  linarith

/-- Construct a jointly continuous inverse on a common ball from a
uniform half-identity approximation in the fiber variable. -/
theorem exists_continuous_parametric_inverse
    (f : P × V → V) (U : Set P) (δ : ℝ) (hδ : 0 < δ)
    (hcont : ContinuousOn f (U ×ˢ closedBall (0 : V) δ))
    (hzero : ∀ p ∈ U, f (p, 0) = 0)
    (happrox : ∀ p ∈ U, ApproximatesLinearOn (fun v => f (p, v))
      (ContinuousLinearMap.id ℝ V) (closedBall (0 : V) δ) (1 / 2)) :
    ∃ inverse : P × V → V,
      ContinuousOn inverse (U ×ˢ closedBall (0 : V) (δ / 2)) ∧
      (∀ p ∈ U, ∀ y ∈ closedBall (0 : V) (δ / 2),
        inverse (p, y) ∈ closedBall (0 : V) δ ∧ f (p, inverse (p, y)) = y) ∧
      ∀ p ∈ U, ∀ x ∈ closedBall (0 : V) δ,
        f (p, x) ∈ closedBall (0 : V) (δ / 2) → inverse (p, f (p, x)) = x := by
  let D := U ×ˢ closedBall (0 : V) (δ / 2)
  let rightInverse : (ContinuousLinearMap.id ℝ V).NonlinearRightInverse := {
    toFun := id
    nnnorm := 1
    bound' := fun _ => by simp
    right_inv' := fun _ => rfl }
  have hsurj (p : P) (hp : p ∈ U) :
      SurjOn (fun x => f (p, x)) (closedBall (0 : V) δ) (closedBall (0 : V) (δ / 2)) := by
    have h := (happrox p hp).surjOn_closedBall_of_nonlinearRightInverse
      rightInverse (le_of_lt hδ) (Subset.refl _)
    simpa only [rightInverse, NNReal.coe_one, inv_one, NNReal.coe_div, NNReal.coe_ofNat,
      hzero p hp, show ((1 : ℝ) - 1 / 2) * δ = δ / 2 by ring] using h
  have hex (q : P × V) : ∃ x, q ∈ D →
      x ∈ closedBall (0 : V) δ ∧ f (q.1, x) = q.2 := by
    by_cases hq : q ∈ D
    · obtain ⟨x, hx, he⟩ := hsurj q.1 hq.1 hq.2
      exact ⟨x, fun _ => ⟨hx, he⟩⟩
    · exact ⟨0, fun h => (hq h).elim⟩
  choose inverse hinv using hex
  have hbound (q q₀ : P × V) (hq : q ∈ D) (hq₀ : q₀ ∈ D) :
      ‖inverse q - inverse q₀‖ ≤ 2 * ‖q.2 - f (q.1, inverse q₀)‖ := by
    have h := approximates_id_inverse_bound (fun x => f (q.1, x)) _ (happrox q.1 hq.1)
      (inverse q) (hinv q hq).1 (inverse q₀) (hinv q₀ hq₀).1
    rw [(hinv q hq).2] at h
    exact h
  refine ⟨inverse, ?_, fun p hp y hy => hinv (p, y) ⟨hp, hy⟩, ?_⟩
  · intro q₀ hq₀
    have hfixed : ContinuousOn (fun q : P × V => f (q.1, inverse q₀)) D :=
      hcont.comp (continuousOn_fst.prodMk continuousOn_const)
        (fun q hq => ⟨hq.1, (hinv q₀ hq₀).1⟩)
    have herr : ContinuousWithinAt (fun q : P × V => 2 * ‖q.2 - f (q.1, inverse q₀)‖) D q₀ :=
      ((continuousOn_snd.sub hfixed).norm.const_mul 2) q₀ hq₀
    have hlim : Tendsto (fun q : P × V => 2 * ‖q.2 - f (q.1, inverse q₀)‖)
        (𝓝[D] q₀) (𝓝 (0 : ℝ)) := by
      change Tendsto _ _ (𝓝 (2 * ‖q₀.2 - f (q₀.1, inverse q₀)‖)) at herr
      simpa only [(hinv q₀ hq₀).2, sub_self, norm_zero, mul_zero] using herr
    change Tendsto inverse (𝓝[D] q₀) (𝓝 (inverse q₀))
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact hbound q q₀ hq hq₀
  · intro p hp x hx hfx
    have hin := hinv (p, f (p, x)) ⟨hp, hfx⟩
    have h := approximates_id_inverse_bound (fun v => f (p, v)) _ (happrox p hp)
      (inverse (p, f (p, x))) hin.1 x hx
    rw [hin.2, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

/-- A continuous vertical derivative equal to the identity at the center
constructs a common continuous inverse near the zero section. -/
theorem exists_local_continuous_parametric_inverse
    (f : P × V → V) (derivative : P × V → V →L[ℝ] V)
    (Ω : Set (P × V)) (hΩ : IsOpen Ω) (p₀ : P) (hp₀ : (p₀, (0 : V)) ∈ Ω)
    (hcont : ContinuousOn f Ω) (hdercont : ContinuousOn derivative Ω)
    (hderiv : ∀ q ∈ Ω, HasFDerivAt (fun v => f (q.1, v)) (derivative q) q.2)
    (hzero : ∀ p, (p, (0 : V)) ∈ Ω → f (p, 0) = 0)
    (hidentity : derivative (p₀, 0) = ContinuousLinearMap.id ℝ V) :
    ∃ (U : Set P) (δ : ℝ) (inverse : P × V → V),
      IsOpen U ∧ p₀ ∈ U ∧ 0 < δ ∧ U ×ˢ closedBall (0 : V) δ ⊆ Ω ∧
      ContinuousOn inverse (U ×ˢ closedBall (0 : V) (δ / 2)) ∧
      (∀ p ∈ U, ∀ y ∈ closedBall (0 : V) (δ / 2),
        inverse (p, y) ∈ closedBall (0 : V) δ ∧ f (p, inverse (p, y)) = y) ∧
      ∀ p ∈ U, ∀ x ∈ closedBall (0 : V) δ,
        f (p, x) ∈ closedBall (0 : V) (δ / 2) → inverse (p, f (p, x)) = x := by
  let Ω' := Ω ∩ {q | ‖derivative q - ContinuousLinearMap.id ℝ V‖ < (1 / 2 : ℝ)}
  have hΩ' : IsOpen Ω' :=
    (hdercont.sub continuousOn_const).norm.isOpen_inter_preimage hΩ isOpen_Iio
  have hp' : (p₀, (0 : V)) ∈ Ω' := by
    refine ⟨hp₀, ?_⟩
    change ‖derivative (p₀, 0) - ContinuousLinearMap.id ℝ V‖ < (1 / 2 : ℝ)
    rw [hidentity, sub_self, norm_zero]
    norm_num
  obtain ⟨U, W, hU, hpU, hW, h0W, hsub⟩ := mem_nhds_prod_iff'.mp (hΩ'.mem_nhds hp')
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds h0W)
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  have hball : closedBall (0 : V) δ ⊆ W := by
    intro v hv
    exact hεW ((mem_closedBall.mp hv).trans_lt (half_lt_self hε))
  have hinto (p : P) (hp : p ∈ U) (v : V) (hv : v ∈ closedBall (0 : V) δ) : (p, v) ∈ Ω' :=
    hsub ⟨hp, hball hv⟩
  have hintoΩ : U ×ˢ closedBall (0 : V) δ ⊆ Ω := fun q hq => (hinto q.1 hq.1 q.2 hq.2).1
  have happrox (p : P) (hp : p ∈ U) : ApproximatesLinearOn (fun v => f (p, v))
      (ContinuousLinearMap.id ℝ V) (closedBall (0 : V) δ) (1 / 2) := by
    have hd (v : V) (hv : v ∈ closedBall (0 : V) δ) :
        HasFDerivWithinAt (fun v => f (p, v) - v)
          (derivative (p, v) - ContinuousLinearMap.id ℝ V) (closedBall (0 : V) δ) v :=
      ((hderiv (p, v) (hinto p hp v hv).1).sub (hasFDerivAt_id v)).hasFDerivWithinAt
    have hb (v : V) (hv : v ∈ closedBall (0 : V) δ) :
        ‖derivative (p, v) - ContinuousLinearMap.id ℝ V‖₊ ≤ (1 / 2 : ℝ≥0) :=
      show ‖derivative (p, v) - ContinuousLinearMap.id ℝ V‖ ≤ (1 / 2 : ℝ) from
        (hinto p hp v hv).2.le
    exact (Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le hd hb
      (convex_closedBall (0 : V) δ)).approximatesLinearOn
  obtain ⟨inverse, hi, hr, hl⟩ := exists_continuous_parametric_inverse f U δ hδ
    (hcont.mono hintoΩ)
    (fun p hp => hzero p (hinto p hp 0 (mem_closedBall_self (le_of_lt hδ))).1) happrox
  exact ⟨U, δ, inverse, hU, hpU, hδ, hintoΩ, hi, hr, hl⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.ParametricInverse.Abelian
