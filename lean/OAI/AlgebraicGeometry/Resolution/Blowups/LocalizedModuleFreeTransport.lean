import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.LocalProperties.Projective

/-! # Localized Module Free Transport -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.LocalizedModuleFreeTransport.Construction

noncomputable section

/-! A local module basis transports to any actual ring and module localization. -/

theorem free_of_actual_localization
    {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (S : Submonoid R) [IsLocalization S A] (f : M →ₗ[R] N) [IsLocalizedModule S f]
    [Module.Free (Localization S) (LocalizedModule S M)] : Module.Free A N := by
  let b := Module.Free.chooseBasis (Localization S) (LocalizedModule S M)
  let e := IsLocalization.algEquiv S (Localization S) A
  let E : N ≃ₗ[R] (Module.Free.ChooseBasisIndex (Localization S) (LocalizedModule S M) →₀ A) :=
    (IsLocalizedModule.iso S f).symm.trans
      ((b.repr.restrictScalars R).trans (Finsupp.mapRange.linearEquiv e.toLinearEquiv))
  exact Module.Free.of_basis (Module.Basis.ofRepr (E.extendScalarsOfIsLocalization S A))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.LocalizedModuleFreeTransport.Construction
