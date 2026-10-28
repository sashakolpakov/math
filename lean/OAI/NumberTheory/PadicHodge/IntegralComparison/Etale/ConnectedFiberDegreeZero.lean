import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DegreeZeroGeneralPullback
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Connected Fiber Degree Zero -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.ConnectedFiberDegreeZero

noncomputable section

/-! Original rational étale degree-zero pullback is an isomorphism along a proper geometrically connected morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {X Y : Scheme.{u}} [NoetherianSpace X] [NoetherianSpace Y]
  (g : X ⟶ Y) [IsProper g] [GeometricallyConnected g]

omit [NoetherianSpace X] [NoetherianSpace Y] in
theorem components_bijective : Function.Bijective (ConnectedComponentSections.map g.base.hom) := by
  exact (g.isClosedMap.isQuotientMap g.continuous g.surjective).isCoinducing.connectedComponentsMap_bijective
    g.isConnected_preimage_singleton

variable (ℓ : ℕ) [Fact ℓ.Prime]

def componentEquiv :
    (_root_.ConnectedComponents Y → ℚ_[ℓ]) ≃ₗ[ℚ_[ℓ]] (_root_.ConnectedComponents X → ℚ_[ℓ]) :=
  LinearEquiv.funCongrLeft ℚ_[ℓ] ℚ_[ℓ]
    (Equiv.ofBijective (ConnectedComponentSections.map g.base.hom) (components_bijective g))

def equiv : Cohomology.RationalEllAdicCohomology ℓ Y 0 ≃ₗ[ℚ_[ℓ]]
    Cohomology.RationalEllAdicCohomology ℓ X 0 :=
  (Etale.ConnectedComponents.equiv ℓ Y).trans
    ((componentEquiv g ℓ).trans (Etale.ConnectedComponents.equiv ℓ X).symm)

theorem equiv_eq_pullback : (equiv g ℓ).toLinearMap = PeriodInvariants.BigEtaleCohomology.pullbackQp ℓ g 0 := by
  apply LinearMap.ext
  intro z
  apply (Etale.ConnectedComponents.equiv ℓ X).injective
  funext c
  change Etale.ConnectedComponents.equiv ℓ X
    ((Etale.ConnectedComponents.equiv ℓ X).symm
      (componentEquiv g ℓ (Etale.ConnectedComponents.equiv ℓ Y z))) c = _
  rw [LinearEquiv.apply_symm_apply]
  exact (DegreeZeroGeneralPullback.pullback_components ℓ g z c).symm

theorem pullback_bijective : Function.Bijective (PeriodInvariants.BigEtaleCohomology.pullbackQp ℓ g 0) := by
  rw [← equiv_eq_pullback]
  exact (equiv g ℓ).bijective

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.ConnectedFiberDegreeZero
