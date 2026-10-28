import Mathlib

/-! # Test Stabilizer -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.TestStabilizer.Realization

noncomputable section

/-! Uniform stabilizers of compactly supported locally constant test functions. -/

open scoped _root_.Topology
open Filter

/-- Compact support upgrades pointwise local constancy to one neighborhood
of the identity fixing the entire function, including outside its support. -/
theorem eventually_test_function_fixed
    {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
    (f : X → ℂ) (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    ∀ᶠ g : G in 𝓝 1, ∀ x : X, f (g • x) = f x := by
  have hK : ∀ᶠ g : G in 𝓝 1, ∀ x ∈ tsupport f, f (g • x) = f x := by
    apply hc.eventually_forall_of_forall_eventually
    intro x _
    have h₁ := (hf.comp_continuous (continuous_smul : Continuous (fun p : G × X => p.1 • p.2))).eventually_eq (1, x)
    have h₂ := (hf.comp_continuous (continuous_snd : Continuous (Prod.snd : G × X → X))).eventually_eq (1, x)
    filter_upwards [h₁, h₂] with p hp₁ hp₂
    simp only [Function.comp_apply, one_smul] at hp₁ hp₂
    exact hp₁.trans hp₂.symm
  have hi : Tendsto (fun g : G => g⁻¹) (𝓝 1) (𝓝 1) := by
    simpa only [inv_one] using (continuous_inv.tendsto (1 : G))
  filter_upwards [hK, hi.eventually hK] with g hg hgi
  intro x
  by_cases hx : f x = 0
  · by_cases hgx : f (g • x) = 0
    · exact hgx.trans hx.symm
    · have h := hgi (g • x) (subset_closure hgx)
      simpa only [inv_smul_smul] using h.symm
  · exact hg x (subset_closure hx)

end

end OAI.RepresentationTheory.Hecke.RadialDilation.TestStabilizer.Realization
