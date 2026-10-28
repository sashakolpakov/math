import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Uniform

/-! # Period Continuation -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.PeriodContinuation.Abelian

noncomputable section

/-!
Continue an actual period by subtracting the local logarithm of its
exponential. The correction is continuous at the central parameter and
vanishes there; the corrected vector lies in the actual exponential kernel.
-/

open Set _root_.Metric Filter
open scoped _root_.Topology

theorem no_small_periods_of_local_logarithm
    {V H : Type} [NormedAddCommGroup V] [Group H]
    (exponential : V → H) (hzero : exponential 0 = 1)
    (coordinates : H → V) (hunit : coordinates 1 = 0)
    (δ : ℝ) (hδ : 0 ≤ δ) (logarithm : V → V)
    (hleft : ∀ v ∈ closedBall (0 : V) δ,
      coordinates (exponential v) ∈ closedBall (0 : V) (δ / 2) →
        logarithm (coordinates (exponential v)) = v) :
    ∀ v ∈ closedBall (0 : V) δ, exponential v = 1 → v = 0 := by
  have hsmall : (0 : V) ∈ closedBall (0 : V) (δ / 2) := mem_closedBall_self (div_nonneg hδ zero_le_two)
  have hlog₀ : logarithm 0 = 0 := by
    have h := hleft 0 (mem_closedBall_self hδ)
    rw [hzero, hunit] at h
    exact h hsmall
  intro v hv he
  have h := hleft v hv
  rw [he, hunit] at h
  exact (h hsmall).symm.trans hlog₀

variable {P V X : Type} [TopologicalSpace P] [NormedAddCommGroup V] [TopologicalSpace X]
  (G : P → Type) [∀ p, Group (G p)]

/-- A common continuous logarithm continues each central period as an
actual period. Its central value and continuity are both retained. -/
theorem exists_continuous_period_extension
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
    (hcont : ContinuousAt (fun p => embed p (exponential p v₀)) p₀) :
    ∃ (U : Set P) (period : P → V),
      IsOpen U ∧ p₀ ∈ U ∧ U ⊆ B ∧ ContinuousAt period p₀ ∧ period p₀ = v₀ ∧
      ∀ p ∈ U, exponential p (period p) = 1 := by
  let φ := fun p => embed p (exponential p v₀)
  let z := fun p => (e (φ p)).2
  have hφ₀ : φ p₀ = embed p₀ 1 := congrArg (embed p₀) hperiod
  have hsource₀ : φ p₀ ∈ e.source := hφ₀ ▸ hunit
  have he₀ : e (φ p₀) = (p₀, (0 : V)) := by rw [hφ₀]; exact hunit₀
  have hz₀ : z p₀ = 0 := congrArg Prod.snd he₀
  have hz : ContinuousAt z p₀ :=
    ((e.continuousOn.continuousAt (e.open_source.mem_nhds hsource₀)).comp hcont).snd
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hs : ∀ᶠ p in 𝓝 p₀, φ p ∈ e.source :=
    hcont.preimage_mem_nhds (e.open_source.mem_nhds hsource₀)
  have hy : ∀ᶠ p in 𝓝 p₀, z p ∈ closedBall (0 : V) (δ / 2) := by
    apply hz.preimage_mem_nhds
    rw [hz₀]
    exact closedBall_mem_nhds _ hδ2
  have hgood : {p | p ∈ B ∧ φ p ∈ e.source ∧ z p ∈ closedBall (0 : V) (δ / 2)} ∈ 𝓝 p₀ := by
    filter_upwards [hB.mem_nhds hp₀, hs, hy] with p hp hs' hy'
    exact ⟨hp, hs', hy'⟩
  obtain ⟨U, hUg, hU, hpU⟩ := mem_nhds_iff.mp hgood
  have hlogAt : ContinuousAt logarithm (p₀, z p₀) := by
    rw [hz₀]
    exact hlog.continuousAt (prod_mem_nhds (hB.mem_nhds hp₀) (closedBall_mem_nhds _ hδ2))
  let period := fun p => v₀ - logarithm (p, z p)
  have hpcont : ContinuousAt period p₀ :=
    continuousAt_const.sub (hlogAt.comp (f := fun p => (p, z p)) (continuousAt_id.prodMk hz))
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

end OAI.ArithmeticGeometry.Descent.CMVariety.PeriodContinuation.Abelian
