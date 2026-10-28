import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SourceTrivializationTop

/-! # Localized Basis Algebra -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalizedBasisAlgebra.Construction.LocalizedBasis

/-!
# Transporting localized bases to arbitrary localization models

The basis obtained by local finite presentation uses canonical localization
types. Coordinate rings of principal scheme opens are different models of
the same localizations; this module transports the basis to those rings.
-/

open _root_.Module

variable {R A R₁ A₁ : Type*} [CommRing R] [CommRing A] [CommRing R₁] [CommRing A₁]
variable [Algebra R A] [Algebra R R₁] [Algebra A A₁] [Algebra R A₁] [Algebra R₁ A₁]
variable [IsScalarTower R A A₁] [IsScalarTower R R₁ A₁]

/-- Any corresponding pair of localization models inherits a basis from
the canonical localized module. -/
noncomputable def algebraBasis (r : R) [IsLocalization.Away r R₁]
    [IsLocalization.Away (algebraMap R A r) A₁]
    {ι : Type*} (b : Basis ι (Localization.Away r) (LocalizedModule.Away r A)) :
    Basis ι R₁ A₁ := by
  let e : Localization.Away r ≃ₐ[R] R₁ := IsLocalization.algEquiv (Submonoid.powers r) _ _
  let : Module R₁ (LocalizedModule.Away r A) :=
    Module.compHom _ e.symm.toRingHom
  have : IsScalarTower R R₁ (LocalizedModule.Away r A) :=
    IsScalarTower.of_algebraMap_smul fun c x => by
      change e.symm (algebraMap R R₁ c) • x = c • x
      rw [e.symm.commutes, IsScalarTower.algebraMap_smul]
  let b' : Basis ι R₁ (LocalizedModule.Away r A) :=
    b.mapCoeffs e.toRingEquiv (fun c x => by
      change e.symm (e c) • x = c • x
      rw [e.symm_apply_apply])
  exact SourceTrivializationTop.Construction.SourceTrivialization.algebraBasis r b'

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalizedBasisAlgebra.Construction.LocalizedBasis
