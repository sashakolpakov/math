import OAI.ArithmeticGeometry.Descent.CMVariety.ExponentialScaling
import OAI.ArithmeticGeometry.Descent.CMVariety.PeriodContinuation

/-! # Continuous Family Periods -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ContinuousFamilyPeriods

noncomputable section

/-! Joint continuity of actual exponential families and period sections
on an open neighborhood, retaining the native exponential kernel. -/

open Set _root_.Metric Filter
open scoped _root_.Manifold ContDiff _root_.Topology NNReal

section Exponentials

variable {P V X : Type}
  [NormedAddCommGroup P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X]
  (E G : P → Type)
  [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)] [∀ p, CompleteSpace (E p)]
  [∀ p, TopologicalSpace (G p)] [∀ p, ChartedSpace (E p) (G p)]
  [∀ p, Group (G p)] [∀ p, LieGroup (𝓘(ℝ, E p)) ∞ (G p)] [∀ p, T2Space (G p)]

theorem continuousOn_exponential_above_zero_section
    (c : ∀ p, OpenPartialHomeomorph (G p) V) (embed : ∀ p, G p → X)
    (power : ℕ → X → X) (hpower : ∀ n, Continuous (power n))
    (hcompat : ∀ n p (g : G p), power n (embed p g) = embed p (g ^ n))
    (U : Set (P × V)) (hU : IsOpen U)
    (hcont : ContinuousOn (fun q : P × V => embed q.1
      (HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp (E := E q.1) (ArithmeticGeometry.Descent.CMVariety.ExponentialChartODE.Abelian.chartVelocity (E := E q.1) (c q.1) q.2))) U) :
    ContinuousOn (fun q : P × V => embed q.1
      (HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp (E := E q.1) (ArithmeticGeometry.Descent.CMVariety.ExponentialChartODE.Abelian.chartVelocity (E := E q.1) (c q.1) q.2)))
      {q | (q.1, (0 : V)) ∈ U} := by
  intro q hq
  exact (ArithmeticGeometry.Descent.CMVariety.ExponentialScaling.Abelian.continuousAt_exponential_of_power_maps E G c embed power hpower hcompat
    q.1 U hU hq hcont q.2).continuousWithinAt

end Exponentials

variable {P V X : Type} [TopologicalSpace P] [NormedAddCommGroup V] [TopologicalSpace X]
  (G : P → Type) [∀ p, Group (G p)]

/-- A common continuous logarithm continues each central period as an
actual period. Its central value and continuity are both retained. -/
theorem exists_continuousOn_period_extension
    (exponential : ∀ p, V → G p)
    (hadd : ∀ p u v, exponential p (u + v) = exponential p u * exponential p v)
    (embed : ∀ p, G p → X) (hembed : ∀ p, Function.Injective (embed p))
    (e : OpenPartialHomeomorph X (P × V))
    (B : Set P) (hB : IsOpen B) (p₀ : P) (hp₀ : p₀ ∈ B)
    (δ : ℝ) (hδ : 0 < δ) (logarithm : P × V → V)
    (hlog : ContinuousOn logarithm (B ×ˢ closedBall (0 : V) (δ / 2)))
    (hlog₀ : logarithm (p₀, 0) = 0)
    (hright : ∀ p ∈ B, ∀ y ∈ closedBall (0 : V) (δ / 2),
      embed p (exponential p (logarithm (p, y))) = e.symm (p, y))
    (hprojection : ∀ p ∈ B, ∀ v, embed p (exponential p v) ∈ e.source →
      (e (embed p (exponential p v))).1 = p)
    (hunit : embed p₀ 1 ∈ e.source) (hunit₀ : e (embed p₀ 1) = (p₀, 0))
    (v₀ : V) (hperiod : exponential p₀ v₀ = 1)
    (hcont : ContinuousOn (fun p => embed p (exponential p v₀)) B) :
    ∃ (U : Set P) (period : P → V),
      IsOpen U ∧ p₀ ∈ U ∧ U ⊆ B ∧ ContinuousOn period U ∧ period p₀ = v₀ ∧
      ∀ p ∈ U, exponential p (period p) = 1 := by
  have hcontAt := hcont.continuousAt (hB.mem_nhds hp₀)
  let φ := fun p => embed p (exponential p v₀)
  let z := fun p => (e (φ p)).2
  have hφ₀ : φ p₀ = embed p₀ 1 := congrArg (embed p₀) hperiod
  have hsource₀ : φ p₀ ∈ e.source := hφ₀ ▸ hunit
  have he₀ : e (φ p₀) = (p₀, (0 : V)) := by rw [hφ₀]; exact hunit₀
  have hz₀ : z p₀ = 0 := congrArg Prod.snd he₀
  have hz : ContinuousAt z p₀ :=
    ((e.continuousOn.continuousAt (e.open_source.mem_nhds hsource₀)).comp hcontAt).snd
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hs : ∀ᶠ p in 𝓝 p₀, φ p ∈ e.source :=
    hcontAt.preimage_mem_nhds (e.open_source.mem_nhds hsource₀)
  have hy : ∀ᶠ p in 𝓝 p₀, z p ∈ closedBall (0 : V) (δ / 2) := by
    apply hz.preimage_mem_nhds
    rw [hz₀]
    exact closedBall_mem_nhds _ hδ2
  have hgood : {p | p ∈ B ∧ φ p ∈ e.source ∧ z p ∈ closedBall (0 : V) (δ / 2)} ∈ 𝓝 p₀ := by
    filter_upwards [hB.mem_nhds hp₀, hs, hy] with p hp hs' hy'
    exact ⟨hp, hs', hy'⟩
  obtain ⟨U, hUg, hU, hpU⟩ := mem_nhds_iff.mp hgood
  let period := fun p => v₀ - logarithm (p, z p)
  have hzOn : ContinuousOn z U :=
    (e.continuousOn.comp (hcont.mono (fun p hp => (hUg hp).1))
      (fun p hp => (hUg hp).2.1)).snd
  have hpcont : ContinuousOn period U := continuousOn_const.sub
    (hlog.comp (continuousOn_id.prodMk hzOn)
      (fun p hp => ⟨(hUg hp).1, (hUg hp).2.2⟩))
  have hpzero : period p₀ = v₀ := by
    change v₀ - logarithm (p₀, z p₀) = v₀
    rw [hz₀, hlog₀, sub_zero]
  refine ⟨U, period, hU, hpU, fun p hp => (hUg hp).1, hpcont, hpzero, ?_⟩
  intro p hp
  have hg := hUg hp
  have he : e (φ p) = (p, z p) := Prod.ext (hprojection p hg.1 v₀ hg.2.1) rfl
  have hinv : e.symm (p, z p) = φ p := by rw [← he, e.left_inv hg.2.1]
  have hexp : exponential p (logarithm (p, z p)) = exponential p v₀ :=
    hembed p ((hright p hg.1 (z p) hg.2.2).trans hinv)
  have h := hadd p (v₀ - logarithm (p, z p)) (logarithm (p, z p))
  rw [sub_add_cancel, hexp] at h
  apply mul_right_cancel (b := exponential p v₀)
  exact h.symm.trans (one_mul _).symm

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ContinuousFamilyPeriods
