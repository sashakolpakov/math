import Mathlib

/-! # Compact Fiber -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CompactFiber.CM

noncomputable section

/-! ThetaCycle: uniform convergence along a compact fiber from joint continuity
at that fiber, together with eventual containment in an open chart. -/

open scoped _root_.Topology
open Filter Set

theorem eventually_compact_fiber_mem
    {P X A : Type*} [TopologicalSpace P] [TopologicalSpace X] {l : Filter A}
    (p : A → P) (p₀ : P) (hp : Tendsto p l (𝓝 p₀))
    (K : Set X) (hK : IsCompact K) (U : Set (P × X)) (hU : IsOpen U)
    (hfiber : ∀ x ∈ K, (p₀, x) ∈ U) :
    ∀ᶠ a in l, ∀ x ∈ K, (p a, x) ∈ U := by
  have hprod : ({p₀} : Set P) ×ˢ K ⊆ U := by
    rintro ⟨q, x⟩ ⟨hq, hx⟩
    rcases Set.mem_singleton_iff.mp hq with rfl
    exact hfiber x hx
  obtain ⟨u, v, hu, _, hpu, hKv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hK hU hprod
  filter_upwards [hp (hu.mem_nhds (hpu (mem_singleton p₀)))] with a ha
  intro x hx
  exact huv ⟨ha, hKv hx⟩

/-- Continuity at the limiting compact fiber is sufficient; continuity away
from it and local compactness of the parameter space are unnecessary. -/
theorem compact_fiber_uniform_limit
    {P X E A : Type*} [TopologicalSpace P] [TopologicalSpace X] [PseudoMetricSpace E]
    {l : Filter A} (p : A → P) (p₀ : P) (hp : Tendsto p l (𝓝 p₀))
    (F : P → X → E) (K : Set X) (hK : IsCompact K)
    (hF : ∀ x ∈ K, ContinuousAt (Function.uncurry F) (p₀, x)) :
    TendstoUniformlyOn (fun a => F (p a)) (F p₀) l K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let U : Set (P × X) := {q | dist (F p₀ q.2) (F q.1 q.2) < ε}
  have hfiber : ∀ x ∈ K, (p₀, x) ∈ interior U := by
    intro x hx
    have hc : ContinuousAt (fun q : P × X => F p₀ q.2) (p₀, x) :=
      (hF x hx).comp (x := (p₀, x)) (f := fun q : P × X => (p₀, q.2))
        (continuous_const.prodMk continuous_snd).continuousAt
    have hd : ContinuousAt (fun q : P × X => dist (F p₀ q.2) (F q.1 q.2)) (p₀, x) :=
      hc.dist (hF x hx)
    apply mem_interior_iff_mem_nhds.mpr
    have hεN : Iio ε ∈ 𝓝 (dist (F p₀ x) (F p₀ x)) := by
      exact isOpen_Iio.mem_nhds (by simpa only [mem_Iio, dist_self] using hε)
    exact hd hεN
  filter_upwards [eventually_compact_fiber_mem p p₀ hp K hK (interior U) isOpen_interior hfiber]
    with a ha
  intro x hx
  exact interior_subset (s := U) (ha x hx)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CompactFiber.CM
