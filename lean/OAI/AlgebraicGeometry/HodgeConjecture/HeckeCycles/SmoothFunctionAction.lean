import Mathlib

/-! # Smooth Function Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SmoothFunctionAction.CM

noncomputable section

/-! Open vector stabilizers give locally constant orbits and continuous
evaluation of the resulting family of continuous functions. -/

open scoped _root_.Topology
open Filter

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] (ρ : G →* (V ≃ₗ[ℂ] V))
  (hρ : ∀ v : V, IsOpen {g : G | ρ g v = v})

include hρ in
theorem orbit (v : V) : IsLocallyConstant (fun g : G => ρ g v) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hf : ∀ᶠ h in 𝓝 (1 : G), ρ h v = v := (hρ v).mem_nhds (by simp)
  have ht : Tendsto (fun h : G => g⁻¹ * h) (𝓝 g) (𝓝 (1 : G)) := by
    have hc : Continuous (fun h : G => g⁻¹ * h) := continuous_const.mul continuous_id
    have h := hc.tendsto g
    rw [inv_mul_cancel] at h
    exact h
  filter_upwards [ht.eventually hf] with h hh
  have he := congrArg (ρ g) hh
  simpa only [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel_left] using he

include hρ in
theorem evaluation {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (ev : V → X → Y) (he : ∀ v : V, Continuous (ev v)) (v : V) :
    Continuous (fun p : G × X => ev (ρ p.1 v) p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hn : ∀ᶠ q : G × X in 𝓝 p, ρ q.1 v = ρ p.1 v :=
    continuous_fst.continuousAt.eventually ((orbit ρ hρ v).eventually_eq p.1)
  apply ((he (ρ p.1 v)).comp continuous_snd).continuousAt.congr_of_eventuallyEq
  filter_upwards [hn] with q hq
  exact congrArg (fun w : V => ev w q.2) hq

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SmoothFunctionAction.CM
