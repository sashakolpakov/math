import OAI.ArithmeticGeometry.Descent.CMVariety.LocalPeriod
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! # Continuous Period Basis -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-!
Continue a central real basis consisting of periods. Openness of linear
isomorphisms gives actual nearby real coordinate isomorphisms; their
basis vectors remain genuine periods and vary continuously at the center.
This does not yet assert that they generate the entire integral lattice.
-/

open Set Filter
open scoped Classical _root_.Topology

variable {P V X Index : Type} [TopologicalSpace P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace X] [Fintype Index]
  {G : P → Type} [∀ p, Group (G p)]
  {exponential : ∀ p, V → G p} {embed : ∀ p, G p → X} {p₀ : P}

theorem LocalPeriod.Abelian.LocalPeriodFamily.exists_continuous_real_period_basis
    (H : LocalPeriod.Abelian.LocalPeriodFamily G exponential embed p₀)
    (e₀ : (Index → ℝ) ≃L[ℝ] V)
    (hperiod : ∀ i, exponential p₀ (e₀ (Pi.single i 1)) = 1) :
    ∃ e : P → (Index → ℝ) ≃L[ℝ] V,
      e p₀ = e₀ ∧ ContinuousAt (fun p => (e p).toContinuousLinearMap) p₀ ∧
      ∀ᶠ p in 𝓝 p₀, ∀ i, exponential p (e p (Pi.single i 1)) = 1 := by
  choose period hcont hcenter hker using fun i => H.continuation _ (hperiod i)
  let frames := ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := V) Index
  let f : P → (Index → ℝ) →L[ℝ] V := fun p => frames.symm (fun i => period i p)
  have hf : ContinuousAt f p₀ :=
    frames.symm.continuous.continuousAt.comp (continuousAt_pi.mpr hcont)
  have hf₀ : f p₀ = e₀.toContinuousLinearMap := by
    apply frames.injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    funext i
    exact hcenter i
  let invertible : Set ((Index → ℝ) →L[ℝ] V) :=
    Set.range (fun e : (Index → ℝ) ≃L[ℝ] V => e.toContinuousLinearMap)
  have hinv : ∀ᶠ p in 𝓝 p₀, f p ∈ invertible := by
    apply hf.preimage_mem_nhds
    rw [hf₀]
    exact e₀.nhds
  have hex (p : P) : ∃ e : (Index → ℝ) ≃L[ℝ] V,
      f p ∈ invertible → e.toContinuousLinearMap = f p := by
    by_cases hp : f p ∈ invertible
    · obtain ⟨e, he⟩ := hp
      exact ⟨e, fun _ => he⟩
    · exact ⟨e₀, fun h => (hp h).elim⟩
  choose e he using hex
  have hevent : (fun p => (e p).toContinuousLinearMap) =ᶠ[𝓝 p₀] f :=
    hinv.mono (fun p hp => he p hp)
  have he₀ : e p₀ = e₀ := by
    ext v
    exact congrArg (fun L : (Index → ℝ) →L[ℝ] V => L v)
      ((hevent.self_of_nhds).trans hf₀)
  refine ⟨e, he₀, hf.congr_of_eventuallyEq hevent, ?_⟩
  have hperiods : ∀ᶠ p in 𝓝 p₀, ∀ i, exponential p (period i p) = 1 :=
    eventually_all.mpr hker
  filter_upwards [hevent, hperiods] with p hp hpk
  intro i
  have hi : e p (Pi.single i 1) = period i p := by
    have h := congrArg (fun L => frames L i) hp
    change e p (Pi.single i 1) = frames (frames.symm (fun j => period j p)) i at h
    rw [ContinuousLinearEquiv.apply_symm_apply] at h
    exact h
  rw [hi]
  exact hpk i

end

end OAI.ArithmeticGeometry.Descent.CMVariety
