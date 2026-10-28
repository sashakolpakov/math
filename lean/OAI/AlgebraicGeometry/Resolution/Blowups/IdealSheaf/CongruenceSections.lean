import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.IdealSheafCongruence
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CongruencePullback

/-! # Congruence Sections -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf

noncomputable section

/-! Restrict intrinsic congruence to the actual section maps on common affine neighborhoods. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem CongruentMaps.Construction.IdealSheafCongruent.appLE {U X : Scheme.{u}} {a b : U ⟶ X} {T : X.IdealSheafData}
    (h : CongruentMaps.Construction.IdealSheafCongruent a b T) (W : X.affineOpens) (V : U.affineOpens)
    (ha : V.1 ≤ a ⁻¹ᵁ W.1) (hb : V.1 ≤ b ⁻¹ᵁ W.1) :
    (T.ideal W).map (a.appLE W.1 V.1 ha).hom = (T.ideal W).map (b.appLE W.1 V.1 hb).hom ∧
      ∀ x : Γ(X, W), (b.appLE W.1 V.1 hb).hom x - (a.appLE W.1 V.1 ha).hom x ∈
        (T.ideal W).map (a.appLE W.1 V.1 ha).hom := by
  let : IsOpenImmersion W.2.fromSpec := W.2.isOpenImmersion_fromSpec
  have hl := h.comp V.2.fromSpec
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec a W.2 V.2 ha,
    ← IsAffineOpen.SpecMap_appLE_fromSpec b W.2 V.2 hb] at hl
  have hr := hl.of_comp_mono W.2.fromSpec T
  rw [Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel] at hr
  exact (Affine.IdealSheafCongruence.Construction.idealSheafCongruent_Spec_iff _ _ _).mp hr

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf
