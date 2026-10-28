import Mathlib.RingTheory.Localization.Free

/-! # Basis Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.BasisTransport

noncomputable section

/-! A basis of the canonical module localization transports to any realization of the localized ring and module. -/
universe u v w z

def localizedBasisTransport {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] (S : Submonoid R)
    {R' : Type w} [CommRing R'] [Algebra R R'] [IsLocalization S R']
    {M' : Type z} [AddCommGroup M'] [Module R M'] [Module R' M'] [IsScalarTower R R' M']
    (f : M →ₗ[R] M') [IsLocalizedModule S f] {ι : Type*}
    (b : Module.Basis ι (Localization S) (LocalizedModule S M)) : Module.Basis ι R' M' := by
  let eR := IsLocalization.algEquiv S (Localization S) R'
  letI : Module (Localization S) M' := Module.compHom M' eR.toRingHom
  haveI : IsScalarTower R (Localization S) M' := by
    constructor
    intro r s m
    change eR (r • s) • m = r • (eR s • m)
    rw [map_smul, smul_assoc]
  let e := IsLocalizedModule.iso S f
  let e' : LocalizedModule S M ≃ₗ[Localization S] M' :=
    { __ := e, toLinearMap := e.toLinearMap.extendScalarsOfIsLocalization S (Localization S) }
  exact (b.map e').mapCoeffs eR.toRingEquiv (fun _ _ => rfl)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.BasisTransport
