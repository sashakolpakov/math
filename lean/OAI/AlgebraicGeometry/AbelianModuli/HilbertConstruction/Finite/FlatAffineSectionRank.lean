import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # Flat Affine Section Rank -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatAffineSectionRank

noncomputable section

/-! The rank of a finite flat scheme map agrees with the rank of its algebra of sections on every affine open. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem affineSection_fromSpec_isPullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    {U : X.Opens} (hU : IsAffineOpen U) (hY : IsAffineOpen (f ⁻¹ᵁ U)) :
    IsPullback hY.fromSpec (Spec.map (f.app U)) f hU.fromSpec := by
  have hw : hY.isoSpec.inv ≫ (f ∣_ U) = Spec.map (f.app U) ≫ hU.isoSpec.inv := by
    apply (cancel_mono U.ι).mp
    have he := hU.SpecMap_appLE_fromSpec f hY (le_refl (f ⁻¹ᵁ U))
    rw [Scheme.Hom.appLE_eq_app] at he
    simpa only [Category.assoc, morphismRestrict_ι, IsAffineOpen.fromSpec] using he.symm
  have hi : IsPullback hY.isoSpec.inv (Spec.map (f.app U)) (f ∣_ U) hU.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨hw⟩
  exact hi.paste_horiz (isPullback_morphismRestrict f U).flip

theorem finiteFlat_affineSection_rank {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [Flat f] {U : X.Opens} (hU : IsAffineOpen U)
    (p : PrimeSpectrum Γ(X, U)) : (f.app U).hom.finrank p = f.finrank (hU.fromSpec p) := by
  have hY : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have hf : (f.app U).hom.Flat := by
    simpa only [Scheme.Hom.appLE_eq_app] using f.flat_appLE hU hY (le_refl (f ⁻¹ᵁ U))
  rw [← Scheme.Hom.finrank_SpecMap_eq_finrank (f.finite_app U hU) hf]
  exact Scheme.Hom.finrank_of_isPullback _ _ _ _ (affineSection_fromSpec_isPullback f hU hY) p

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatAffineSectionRank
