import OAI.ArithmeticGeometry.Descent.CMVariety.ContinuousPeriodBasis
import Mathlib.Topology.Compactness.Compact

/-! # Fundamental Period Cube -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-!
Compactness of a fixed coordinate cube rules out new periods in the
continued real basis. Near its origin the uniform small-kernel estimate
applies; elsewhere the closed identity locus and actual exponential
continuity exclude a period. A finite compactness argument makes this
exclusion simultaneous for all coefficients in the cube.
-/

open Set _root_.Metric Filter
open scoped Classical _root_.Topology

variable {P V X Index : Type} [TopologicalSpace P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace X] [Fintype Index]
  {G : P → Type} [∀ p, Group (G p)]
  {exponential : ∀ p, V → G p} {embed : ∀ p, G p → X} {p₀ : P}

theorem LocalPeriod.Abelian.LocalPeriodFamily.eventually_fundamental_cube_kernel_free
    (H : LocalPeriod.Abelian.LocalPeriodFamily G exponential embed p₀)
    (identityLocus : Set X) (hclosed : IsClosed identityLocus)
    (hmembership : ∀ p v, embed p (exponential p v) ∈ identityLocus ↔ exponential p v = 1)
    (e : P → (Index → ℝ) ≃L[ℝ] V)
    (he : ContinuousAt (fun p => (e p).toContinuousLinearMap) p₀)
    (hcentral : ∀ t ∈ closedBall (0 : Index → ℝ) (1 / 2), exponential p₀ (e p₀ t) = 1 → t = 0) :
    ∀ᶠ p in 𝓝 p₀, ∀ t ∈ closedBall (0 : Index → ℝ) (1 / 2),
      exponential p (e p t) = 1 → t = 0 := by
  apply (isCompact_closedBall (0 : Index → ℝ) (1 / 2)).eventually_forall_of_forall_eventually
  intro t ht
  have hlinear : ContinuousAt (fun q : P × (Index → ℝ) => (e q.1).toContinuousLinearMap) (p₀, t) :=
    he.comp (f := fun q : P × (Index → ℝ) => q.1) (x := (p₀, t)) continuousAt_fst
  have heval : ContinuousAt (fun q : P × (Index → ℝ) => e q.1 q.2) (p₀, t) :=
    hlinear.clm_apply continuousAt_snd
  by_cases ht0 : t = 0
  · subst t
    obtain ⟨B, hB, δ, hδ, hsmall⟩ := H.smallKernel
    have hbase : ∀ᶠ q : P × (Index → ℝ) in 𝓝 (p₀, 0), q.1 ∈ B :=
      continuousAt_fst.preimage_mem_nhds hB
    have hnorm : ∀ᶠ q : P × (Index → ℝ) in 𝓝 (p₀, 0), e q.1 q.2 ∈ closedBall (0 : V) δ := by
      apply heval.preimage_mem_nhds
      rw [map_zero]
      exact closedBall_mem_nhds _ hδ
    filter_upwards [hbase, hnorm] with q hq hnormq
    intro hker
    apply (e q.1).injective
    exact (hsmall q.1 hq _ hnormq hker).trans (map_zero (e q.1)).symm
  · have hφ : ContinuousAt
        (fun q : P × (Index → ℝ) => embed q.1 (exponential q.1 (e q.1 q.2))) (p₀, t) :=
      (H.continuous (e p₀ t)).comp
        (f := fun q : P × (Index → ℝ) => (q.1, e q.1 q.2))
        (g := fun q : P × V => embed q.1 (exponential q.1 q.2))
        (x := (p₀, t)) (continuousAt_fst.prodMk heval)
    have hnot : embed p₀ (exponential p₀ (e p₀ t)) ∈ identityLocusᶜ := by
      intro hmem
      exact ht0 (hcentral t ht ((hmembership p₀ (e p₀ t)).mp hmem))
    have hnear := hφ.preimage_mem_nhds (hclosed.isOpen_compl.mem_nhds hnot)
    filter_upwards [hnear] with q hq
    intro hker
    exact False.elim (hq ((hmembership q.1 (e q.1 q.2)).mpr hker))

end

end OAI.ArithmeticGeometry.Descent.CMVariety
