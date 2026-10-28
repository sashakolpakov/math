import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedOpenFactors
import OAI.RepresentationTheory.Theta.Adelic.TensorProjective

/-! # Restricted Smooth Unramified -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedSmoothUnramified.CM

noncomputable section

/-! A smooth restricted-product representation fixes every specified
vector under almost all supported integral local subgroups. -/

open scoped Classical RestrictedProduct
open Filter

variable {I : Type*} {G : I → Type*} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  (K : ∀ i, Subgroup (G i)) {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K →* (V ≃ₗ[ℂ] V))
  (hρ : ∀ v : V, IsOpen {g : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K | ρ g v = v})

include hρ in
theorem eventually_fixed (v : V) :
    ∀ᶠ i in Filter.cofinite, ∀ g ∈ K i, ρ (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace K i g) v = v := by
  let U : OpenSubgroup (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K) :=
    ⟨RepresentationTheory.Theta.Adelic.TensorProjective.Smoothness.vectorStabilizer ρ v, hρ v⟩
  exact RestrictedOpenFactors.CM.cofinite K U

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedSmoothUnramified.CM
