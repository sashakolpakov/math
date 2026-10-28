import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.ConfigurationOrbits
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.NormalizedRepresentatives

/-! # Orbit Point Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.OrbitPointEquivalence

noncomputable section

/-! The balanced affine chart represents the orbit set of vector
configurations with its denominator invertible, over every coefficient
algebra. Surjectivity uses the actual normalized chart coordinates. -/
open scoped Classical
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A] {r m : ℕ}

def balancedChartOrbitPointEquiv (hr : 0 < r)
    (i : Fin m) (σ : Fin r → Fin m) (e : Fin m) (c : Fin m → Fin r)
    (a : (Fin r → Fin m) → ℕ) (C : Fin m → (Fin r → Fin m) → ℕ)
    (ha : a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hC : ∀ z, C z + Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z) = a)
    (hframe : Frame.ChartDenominators.frameDiscriminantExponent σ e ≤ a) :
    Quotient (ConfigurationOrbits.balancedChartConfigurationSetoid A a) ≃
      (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i a ha →ₐ[R] A) := by
  let F : Quotient (ConfigurationOrbits.balancedChartConfigurationSetoid A a) →
      (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i a ha →ₐ[R] A) :=
    Quotient.lift (ConfigurationOrbits.balancedConfigurationChartAlgebraEvaluation (R := R) A a i ha)
      (fun _ _ h => ConfigurationOrbits.balancedConfigurationChartAlgebraEvaluation_eq_of_orbit A a hr i ha h)
  have hF : Function.Injective F := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro v w h
    apply Quotient.sound
    exact FiberOrbits.balancedChart_equal_evaluation_implies_same_orbit (R := R) i σ e c a C ha hC hframe
      v.vector w.vector v.denominatorUnit w.denominatorUnit (congrArg AlgHom.toRingHom h)
  have hsurj : Function.Surjective F := by
    intro ρ
    obtain ⟨w, hw, hpoint, _⟩ := NormalizedRepresentatives.balancedChartPoint_has_normalized_configuration
      R hr i σ e c a C ha hC hframe ρ
    refine ⟨Quotient.mk (ConfigurationOrbits.balancedChartConfigurationSetoid A a) ⟨w, hw⟩, ?_⟩
    apply AlgHom.ext
    intro x
    exact RingHom.congr_fun hpoint x
  exact Equiv.ofBijective F ⟨hF, hsurj⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.OrbitPointEquivalence
