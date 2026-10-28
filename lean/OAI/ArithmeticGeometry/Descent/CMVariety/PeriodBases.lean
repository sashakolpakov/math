import OAI.ArithmeticGeometry.Descent.CMVariety.FundamentalPeriodCube
import OAI.ArithmeticGeometry.Descent.CMVariety.LatticeCubeBasis

/-! # Period Bases -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-!
Combine actual period continuation, compactness of the fundamental cube,
and integer rounding to construct full nearby integral period bases.
Their real coordinate isomorphisms are continuous at the central point.
-/

open Set _root_.Metric Filter
open scoped Classical _root_.Topology

variable {P V X Index : Type} [TopologicalSpace P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace X] [Fintype Index]
  {G : P → Type} [∀ p, Group (G p)]
  {exponential : ∀ p, V → G p} {embed : ∀ p, G p → X} {p₀ : P}

/-- The continued real frame is an actual full integral basis of each
nearby exponential kernel. Fullness is proved by the compact cube argument. -/
theorem LocalPeriod.Abelian.LocalPeriodFamily.exists_continuous_full_period_bases
    (H : LocalPeriod.Abelian.LocalPeriodFamily G exponential embed p₀)
    (Λ : P → Submodule ℤ V) (hΛ : ∀ p v, v ∈ Λ p ↔ exponential p v = 1)
    (identityLocus : Set X) (hclosed : IsClosed identityLocus)
    (hmembership : ∀ p v, embed p (exponential p v) ∈ identityLocus ↔ exponential p v = 1)
    (b₀ : Module.Basis Index ℤ (Λ p₀)) (e₀ : (Index → ℝ) ≃L[ℝ] V)
    (hb₀ : ∀ i, (b₀ i : V) = e₀ (Pi.single i 1)) :
    ∃ e : P → (Index → ℝ) ≃L[ℝ] V,
      e p₀ = e₀ ∧ ContinuousAt (fun p => (e p).toContinuousLinearMap) p₀ ∧
      ∀ᶠ p in 𝓝 p₀, ∃ b : Module.Basis Index ℤ (Λ p),
        ∀ i, (b i : V) = e p (Pi.single i 1) := by
  have hperiod (i : Index) : exponential p₀ (e₀ (Pi.single i 1)) = 1 := by
    apply (hΛ _ _).mp
    rw [← hb₀]
    exact (b₀ i).property
  obtain ⟨e, he₀, he, hperiods⟩ := H.exists_continuous_real_period_basis e₀ hperiod
  have hcentral : ∀ t ∈ closedBall (0 : Index → ℝ) (1 / 2), exponential p₀ (e p₀ t) = 1 → t = 0 := by
    intro t ht hker
    rw [he₀] at hker
    exact LatticeCubeBasis.Abelian.integral_basis_fundamental_cube_kernel_free (Λ p₀) b₀ e₀ hb₀ t ht ((hΛ _ _).mpr hker)
  have hcube := H.eventually_fundamental_cube_kernel_free identityLocus hclosed hmembership e he hcentral
  refine ⟨e, he₀, he, ?_⟩
  filter_upwards [hperiods, hcube] with p hp hc
  exact LatticeCubeBasis.Abelian.exists_integral_basis_of_fundamental_cube (Λ p) (e p)
    (fun i => (hΛ _ _).mpr (hp i)) (fun t ht hmem => hc t ht ((hΛ _ _).mp hmem))

end

end OAI.ArithmeticGeometry.Descent.CMVariety
