import OAI.ArithmeticGeometry.Descent.CMVariety.PeriodContinuation

/-! # Local Period -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.LocalPeriod.Abelian

noncomputable section

/-!
Local period properties obtained from the constructed logarithm. The
package retains the actual exponential and total-space inclusion, joint
continuity at every central velocity, uniform kernel exclusion, and
continuation of each central period.
-/

open Set _root_.Metric Filter
open scoped _root_.Topology

variable {P V X : Type} [TopologicalSpace P] [NormedAddCommGroup V] [TopologicalSpace X]
  (G : P → Type) [∀ p, Group (G p)]

/-- Proven local information about the kernels of a genuine exponential
family. This is constructed from a logarithm in the theorem below. -/
structure LocalPeriodFamily
    (exponential : ∀ p, V → G p) (embed : ∀ p, G p → X) (p₀ : P) : Prop where
  zero : ∀ p, exponential p 0 = 1
  add : ∀ p u v, exponential p (u + v) = exponential p u * exponential p v
  inclusion : ∀ p, Function.Injective (embed p)
  continuous : ∀ v : V, ContinuousAt
    (fun q : P × V => embed q.1 (exponential q.1 q.2)) (p₀, v)
  smallKernel : ∃ B : Set P, B ∈ 𝓝 p₀ ∧ ∃ δ : ℝ, 0 < δ ∧
    ∀ p ∈ B, ∀ v ∈ closedBall (0 : V) δ, exponential p v = 1 → v = 0
  continuation : ∀ v : V, exponential p₀ v = 1 →
    ∃ period : P → V, ContinuousAt period p₀ ∧ period p₀ = v ∧
      ∀ᶠ p in 𝓝 p₀, exponential p (period p) = 1

theorem localPeriodFamily_of_logarithm
    (exponential : ∀ p, V → G p) (hzero : ∀ p, exponential p 0 = 1)
    (hadd : ∀ p u v, exponential p (u + v) = exponential p u * exponential p v)
    (embed : ∀ p, G p → X) (hembed : ∀ p, Function.Injective (embed p))
    (p₀ : P) (hcont : ∀ v : V, ContinuousAt
      (fun q : P × V => embed q.1 (exponential q.1 q.2)) (p₀, v))
    (coordinates : ∀ p, G p → V) (e : OpenPartialHomeomorph X (P × V))
    (B : Set P) (hB : IsOpen B) (hp₀ : p₀ ∈ B)
    (hcoordinates₀ : ∀ p ∈ B, coordinates p 1 = 0)
    (δ : ℝ) (hδ : 0 < δ) (logarithm : P × V → V)
    (hlog : ContinuousOn logarithm (B ×ˢ closedBall (0 : V) (δ / 2)))
    (hright : ∀ p ∈ B, ∀ y ∈ closedBall (0 : V) (δ / 2),
      embed p (exponential p (logarithm (p, y))) = e.symm (p, y))
    (hleft : ∀ p ∈ B, ∀ v ∈ closedBall (0 : V) δ,
      coordinates p (exponential p v) ∈ closedBall (0 : V) (δ / 2) →
        logarithm (p, coordinates p (exponential p v)) = v)
    (hprojection : ∀ p ∈ B, ∀ v, embed p (exponential p v) ∈ e.source →
      (e (embed p (exponential p v))).1 = p)
    (hunit : embed p₀ 1 ∈ e.source) (hunit₀ : e (embed p₀ 1) = (p₀, 0)) :
    LocalPeriodFamily G exponential embed p₀ := by
  refine ⟨hzero, hadd, hembed, hcont, ⟨B, hB.mem_nhds hp₀, δ, hδ, ?_⟩, ?_⟩
  · intro p hp
    exact PeriodContinuation.Abelian.no_small_periods_of_local_logarithm (exponential p) (hzero p)
      (coordinates p) (hcoordinates₀ p hp) δ (le_of_lt hδ) (fun y => logarithm (p, y)) (hleft p hp)
  · intro v hv
    have hlog₀ : logarithm (p₀, 0) = 0 := by
      have h := hleft p₀ hp₀ 0 (mem_closedBall_self (le_of_lt hδ))
      rw [hzero p₀, hcoordinates₀ p₀ hp₀] at h
      exact h (mem_closedBall_self (le_of_lt (half_pos hδ)))
    have hfixed : ContinuousAt (fun p => embed p (exponential p v)) p₀ :=
      (hcont v).comp (f := fun p : P => (p, v)) (continuousAt_id.prodMk continuousAt_const)
    obtain ⟨U, period, hU, hpU, _, hpcont, hpzero, hpker⟩ :=
      PeriodContinuation.Abelian.exists_continuous_period_extension G exponential hadd embed hembed e B hB p₀ hp₀
        δ hδ logarithm hlog hlog₀ hright hprojection hunit hunit₀ v hv hfixed
    exact ⟨period, hpcont, hpzero, Filter.mem_of_superset (hU.mem_nhds hpU) hpker⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.LocalPeriod.Abelian
