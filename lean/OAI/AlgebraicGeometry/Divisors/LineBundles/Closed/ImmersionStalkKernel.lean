import OAI.AlgebraicGeometry.Divisors.LineBundles.SurjectiveLocalizationKernel
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Immersion Stalk Kernel -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ImmersionStalkKernel.BundleCycles

noncomputable section

/-! The actual stalk kernel of a closed immersion is obtained by
localizing its affine equation ideal. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.Opens) (hU : IsAffineOpen U) (z : Z) (hz : i z ∈ U)

include hU in
theorem closedImmersion_stalk_kernel :
    RingHom.ker (i.stalkMap z).hom =
      (RingHom.ker (i.app U).hom).map (X.presheaf.germ U (i z) hz).hom := by
  let V := i ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage i
  let P := (hU.primeIdealOf ⟨i z, hz⟩).asIdeal
  let Q := (hV.primeIdealOf ⟨z, hz⟩).asIdeal
  let : Algebra Γ(X, U) (X.presheaf.stalk (i z)) := X.presheaf.algebra_section_stalk ⟨i z, hz⟩
  let : Algebra Γ(Z, V) (Z.presheaf.stalk z) := Z.presheaf.algebra_section_stalk ⟨z, hz⟩
  let : IsLocalization P.primeCompl (X.presheaf.stalk (i z)) := hU.isLocalization_stalk ⟨i z, hz⟩
  let : IsLocalization Q.primeCompl (Z.presheaf.stalk z) := hV.isLocalization_stalk ⟨z, hz⟩
  have hpq : Q.comap (i.app U).hom = P := by
    have h := congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV le_rfl (x := z) hz)
    change Q.comap (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom = P at h
    rwa [Scheme.Hom.appLE_eq_app] at h
  exact SurjectiveLocalizationKernel.BundleCycles.surjectiveLocalization_kernel P Q (i.app U).hom (i.app_surjective U hU) hpq (i.stalkMap z).hom
    (by ext r; exact i.germ_stalkMap_apply U z hz r)

include hU in
theorem closedImmersion_principal_stalk_kernel (t : Γ(X, U))
    (ht : RingHom.ker (i.app U).hom = Ideal.span {t}) :
    RingHom.ker (i.stalkMap z).hom = Ideal.span {X.presheaf.germ U (i z) hz t} := by
  rw [closedImmersion_stalk_kernel i U hU z hz, ht, Ideal.map_span, Set.image_singleton]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ImmersionStalkKernel.BundleCycles
