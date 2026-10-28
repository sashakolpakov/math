import OAI.RepresentationTheory.Hecke.RadialDilation.TestStabilizer

/-! # Continuous Test Families -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.ContinuousTestFamilies.Realization

noncomputable section

/-! Uniform stabilization for continuous families of coordinate changes. -/

open scoped _root_.Topology
open Filter

theorem eventually_compact_test_agrees
    {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    (a₀ : A) (F : A × X → X) (hF : Continuous F) (h₀ : ∀ x, F (a₀, x) = x)
    (f : X → ℂ) (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    ∀ᶠ a in 𝓝 a₀, ∀ x ∈ tsupport f, f (F (a, x)) = f x := by
  apply hc.eventually_forall_of_forall_eventually
  intro x _
  have h₁ := (hf.comp_continuous hF).eventually_eq (a₀, x)
  have h₂ := (hf.comp_continuous (continuous_snd : Continuous (Prod.snd : A × X → X))).eventually_eq (a₀, x)
  filter_upwards [h₁, h₂] with p hp₁ hp₂
  simp only [Function.comp_apply, h₀] at hp₁ hp₂
  exact hp₁.trans hp₂.symm

theorem eventually_homeomorph_test_fixed
    {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    (a₀ : A) (e : A → X ≃ₜ X) (he₀ : e a₀ = Homeomorph.refl X)
    (he : Continuous (fun p : A × X => e p.1 p.2))
    (hi : Continuous (fun p : A × X => (e p.1).symm p.2))
    (f : X → ℂ) (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    ∀ᶠ a in 𝓝 a₀, ∀ x, f (e a x) = f x := by
  have h₀ x : e a₀ x = x := by rw [he₀]; rfl
  have hi₀ x : (e a₀).symm x = x := by rw [he₀]; rfl
  filter_upwards [eventually_compact_test_agrees a₀ _ he h₀ f hf hc,
    eventually_compact_test_agrees a₀ _ hi hi₀ f hf hc] with a ha hai
  intro x
  by_cases hx : f x = 0
  · by_cases hex : f (e a x) = 0
    · exact hex.trans hx.symm
    · have h := hai (e a x) (subset_tsupport f hex)
      simpa only [Homeomorph.symm_apply_apply] using h.symm
  · exact ha x (subset_tsupport f hx)

theorem eventually_compact_phase_one
    {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    (a₀ : A) (F : A × X → ℂ) (hF : IsLocallyConstant F) (h₀ : ∀ x, F (a₀, x) = 1)
    (C : Set X) (hC : IsCompact C) :
    ∀ᶠ a in 𝓝 a₀, ∀ x ∈ C, F (a, x) = 1 := by
  apply hC.eventually_forall_of_forall_eventually
  intro x _
  filter_upwards [hF.eventually_eq (a₀, x)] with p hp
  exact hp.trans (h₀ x)

end

end OAI.RepresentationTheory.Hecke.RadialDilation.ContinuousTestFamilies.Realization
