import Mathlib.RingTheory.Localization.Free

/-! # Module Freeness Transfer -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.ModuleFreenessTransfer

noncomputable section

/-! Freeness transfers from the standard localized module to any actual
localization of the same module, with its native localized-ring action. -/

universe u v w

theorem free_of_isLocalizedModule_of_free_canonical
    {R : Type u} [CommRing R] (S : Submonoid R)
    {M : Type v} [AddCommGroup M] [Module R M]
    (A : Type w) [CommRing A] [Algebra R A] [IsLocalization S A]
    {N : Type*} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (g : M →ₗ[R] N) [IsLocalizedModule S g]
    [Module.Free (Localization S) (LocalizedModule S M)] : Module.Free A N := by
  let eA : Localization S ≃ₐ[R] A := IsLocalization.algEquiv S (Localization S) A
  let eR : LocalizedModule S M ≃ₗ[R] N := IsLocalizedModule.iso S g
  let : RingHomInvPair eA.toRingHom eA.symm.toRingHom :=
    ⟨by ext r; exact eA.symm_apply_apply r, by ext r; exact eA.apply_symm_apply r⟩
  let : RingHomInvPair eA.symm.toRingHom eA.toRingHom :=
    ⟨by ext r; exact eA.apply_symm_apply r, by ext r; exact eA.symm_apply_apply r⟩
  let : Module (Localization S) N := Module.compHom N eA.toRingHom
  have : IsScalarTower R (Localization S) N := .of_algebraMap_smul fun r n => by
    change eA (algebraMap R (Localization S) r) • n = r • n
    rw [eA.commutes, IsScalarTower.algebraMap_smul]
  let l := eR.toLinearMap.extendScalarsOfIsLocalization S (Localization S)
  let e : LocalizedModule S M ≃ₛₗ[eA.toRingHom] N :=
    { eR.toEquiv with
      map_add' := eR.map_add
      map_smul' := fun r m => l.map_smul r m }
  exact Module.Free.of_equiv (σ' := eA.symm.toRingHom) e

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.ModuleFreenessTransfer
