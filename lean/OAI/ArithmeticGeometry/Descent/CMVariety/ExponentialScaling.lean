import OAI.ArithmeticGeometry.Descent.CMVariety.LocalExponentialFamily
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Exponential Scaling -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.ExponentialScaling.Abelian

noncomputable section

/-!
Rescale the constructed time-dependent exponential to time one, then
extend its continuity to arbitrary tangent velocities using continuous
power maps on the total space.
-/

open Set _root_.Metric Filter
open scoped _root_.Manifold ContDiff _root_.Topology NNReal

section OneFiber

variable {E V G : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ∞ G]

omit [LieGroup (𝓘(ℝ, E)) ∞ G] in
theorem chartVelocity_smul (c : OpenPartialHomeomorph G V) (a : ℝ) (v : V) :
    ExponentialChartODE.Abelian.chartVelocity (E := E) c (a • v) = a • ExponentialChartODE.Abelian.chartVelocity (E := E) c v := by
  exact map_smul (mfderiv (𝓘(ℝ, V)) (𝓘(ℝ, E)) c.symm 0) a v

variable [CompleteSpace E] [T2Space G]

theorem exp_nat_smul (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (n : ℕ) :
    AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp ((n : ℝ) • v) = AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp v ^ n := by
  rw [AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp_smul]
  induction n with
  | zero => simp only [Nat.cast_zero, AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.curve_zero, pow_zero]
  | succ n hn =>
    rw [Nat.cast_succ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.curve_add, hn, pow_succ]
    rfl

end OneFiber

variable {P V X : Type}
  [NormedAddCommGroup P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X]
  (E G : P → Type)
  [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)] [∀ p, CompleteSpace (E p)]
  [∀ p, TopologicalSpace (G p)] [∀ p, ChartedSpace (E p) (G p)]
  [∀ p, Group (G p)] [∀ p, LieGroup (𝓘(ℝ, E p)) ∞ (G p)] [∀ p, T2Space (G p)]

/-- A positive time slice and scalar reparametrization give continuity
of the actual time-one exponential on an open tangent neighborhood. -/
theorem exists_open_exponential_neighborhood
    (c : ∀ p, OpenPartialHomeomorph (G p) V) (embed : ∀ p, G p → X)
    (p₀ : P) (r : ℝ≥0) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε)
    (hcont : ContinuousOn
      (fun z : (P × V) × ℝ => embed z.1.1
        (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp (E := E z.1.1) (z.2 • ExponentialChartODE.Abelian.chartVelocity (E := E z.1.1) (c z.1.1) z.1.2)))
      (closedBall (p₀, (0 : V)) r ×ˢ Ioo (-ε) ε)) :
    ∃ U : Set (P × V), IsOpen U ∧ (p₀, (0 : V)) ∈ U ∧
      ContinuousOn (fun q : P × V => embed q.1
        (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp (E := E q.1) (ExponentialChartODE.Abelian.chartVelocity (E := E q.1) (c q.1) q.2))) U := by
  let t := ε / 2
  have ht : 0 < t := half_pos hε
  have htε : t ∈ Ioo (-ε) ε := by constructor <;> dsimp [t] <;> linarith
  let scale : P × V → P × V := fun q => (q.1, t⁻¹ • q.2)
  have hscale : Continuous scale := continuous_fst.prodMk (continuous_const.smul continuous_snd)
  let U := scale ⁻¹' ball (p₀, (0 : V)) (r : ℝ)
  have hU : IsOpen U := isOpen_ball.preimage hscale
  have hcenter : (p₀, (0 : V)) ∈ U := by
    change (p₀, t⁻¹ • (0 : V)) ∈ ball (p₀, 0) (r : ℝ)
    simpa only [smul_zero, mem_ball, dist_self] using (show (0 : ℝ) < r from hr)
  have hc : ContinuousOn
      (fun q : P × V => embed q.1
        (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp (E := E q.1) (t • ExponentialChartODE.Abelian.chartVelocity (E := E q.1) (c q.1) (t⁻¹ • q.2)))) U :=
    hcont.comp (hscale.prodMk continuous_const).continuousOn
      (fun _ hq => ⟨ball_subset_closedBall hq, htε⟩)
  refine ⟨U, hU, hcenter, hc.congr ?_⟩
  intro q _
  dsimp only
  rw [chartVelocity_smul (E := E q.1), smul_smul, mul_inv_cancel₀ (ne_of_gt ht), one_smul]

/-- Continuous algebraic power maps extend exponential continuity from
a neighborhood of zero to every tangent velocity over the central base. -/
theorem continuousAt_exponential_of_power_maps
    (c : ∀ p, OpenPartialHomeomorph (G p) V) (embed : ∀ p, G p → X)
    (power : ℕ → X → X) (hpower : ∀ n, Continuous (power n))
    (hcompat : ∀ n p (g : G p), power n (embed p g) = embed p (g ^ n))
    (p₀ : P) (U : Set (P × V)) (hU : IsOpen U) (hcenter : (p₀, (0 : V)) ∈ U)
    (hcont : ContinuousOn (fun q : P × V => embed q.1
      (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp (E := E q.1) (ExponentialChartODE.Abelian.chartVelocity (E := E q.1) (c q.1) q.2))) U)
    (v₀ : V) :
    ContinuousAt (fun q : P × V => embed q.1
      (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp (E := E q.1) (ExponentialChartODE.Abelian.chartVelocity (E := E q.1) (c q.1) q.2))) (p₀, v₀) := by
  have hlim : Tendsto (fun n : ℕ => (p₀, ((n : ℝ) + 1)⁻¹ • v₀)) atTop (𝓝 (p₀, (0 : V))) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const v₀
    simpa only [one_div, zero_smul] using tendsto_const_nhds.prodMk_nhds h
  obtain ⟨n, hn⟩ := (hlim.eventually (hU.mem_nhds hcenter)).exists
  change (p₀, ((n : ℝ) + 1)⁻¹ • v₀) ∈ U at hn
  let k := n + 1
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  have hmem : (p₀, (k : ℝ)⁻¹ • v₀) ∈ U := by simpa only [k, Nat.cast_add, Nat.cast_one] using hn
  have hscale : Continuous (fun q : P × V => (q.1, (k : ℝ)⁻¹ • q.2)) :=
    continuous_fst.prodMk (continuous_const.smul continuous_snd)
  have hlocal := (hcont.continuousAt (hU.mem_nhds hmem)).comp
    (f := fun q : P × V => (q.1, (k : ℝ)⁻¹ • q.2)) (x := (p₀, v₀)) hscale.continuousAt
  have heq (q : P × V) : power k (embed q.1
      (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp (E := E q.1) (ExponentialChartODE.Abelian.chartVelocity (E := E q.1) (c q.1) ((k : ℝ)⁻¹ • q.2)))) =
        embed q.1 (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp (E := E q.1) (ExponentialChartODE.Abelian.chartVelocity (E := E q.1) (c q.1) q.2)) := by
    rw [hcompat, ← exp_nat_smul, chartVelocity_smul, smul_smul, mul_inv_cancel₀ hk, one_smul]
  have hfinal := (hpower k).continuousAt.comp hlocal
  apply hfinal.congr_of_eventuallyEq
  exact Eventually.of_forall (fun q => (heq q).symm)

end

end OAI.ArithmeticGeometry.Descent.CMVariety.ExponentialScaling.Abelian
