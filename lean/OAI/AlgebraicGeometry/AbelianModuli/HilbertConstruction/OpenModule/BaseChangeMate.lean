import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Base Change Mate -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.BaseChangeMate.OpenPullbackSquare

noncomputable section

/-! The canonical base-change mate for restriction to an open subscheme is invertible. -/
open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

/-- Direct images along the two equal composite scheme morphisms agree. -/
def pushforwardSquareIso :
    Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward (f ∣_ U) ⋙ Scheme.Modules.pushforward U.ι :=
  Scheme.Modules.pushforwardComp (f ⁻¹ᵁ U).ι f ≪≫
    Scheme.Modules.pushforwardCongr (morphismRestrict_ι f U).symm ≪≫
    (Scheme.Modules.pushforwardComp (f ∣_ U) U.ι).symm

/-- The base-change map as a mate across open-restriction adjunctions. -/
def openBaseChangeMap :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor U.ι ⟶
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward (f ∣_ U) :=
  ((mateEquiv (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι)
    (Scheme.Modules.restrictAdjunction U.ι)).symm
      (TwoSquare.mk _ _ _ _ (pushforwardSquareIso f U).hom)).natTrans

/-- The mate is computed using the unit on the inverse-image open and
the counit on the base open. -/
theorem openBaseChangeMap_app (M : X.Modules) :
    (openBaseChangeMap f U).app M =
      (Scheme.Modules.restrictFunctor U.ι).map
        ((Scheme.Modules.pushforward f).map
          ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M)) ≫
      (Scheme.Modules.restrictFunctor U.ι).map
        ((pushforwardSquareIso f U).hom.app
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj M)) ≫
      (Scheme.Modules.restrictAdjunction U.ι).counit.app
        ((Scheme.Modules.pushforward (f ∣_ U)).obj
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj M)) := by
  dsimp [openBaseChangeMap, mateEquiv]
  simp only [Category.id_comp, Category.comp_id]
  erw [(Scheme.Modules.restrictFunctor U.ι).map_id,
    (Scheme.Modules.restrictFunctor U.ι).map_id, Category.id_comp, Category.id_comp]

/-- Restriction does not change the underlying map on the image open. -/
theorem restrict_map_app {Z W : Scheme.{u}} (i : Z ⟶ W) [IsOpenImmersion i]
    {M N : W.Modules} (a : M ⟶ N) (V : Z.Opens) :
    ((Scheme.Modules.restrictFunctor i).map a).app V = a.app (i ''ᵁ V) := rfl

/-- Over the base open, the unit for its inverse-image open is an
isomorphism on direct images. -/
theorem restrictedUnit_isIso (M : X.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.pushforward f).map
        ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M))) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro W
  rw [restrict_map_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictAdjunction_unit_app_app]
  let V := f ⁻¹ᵁ U
  let O := f ⁻¹ᵁ (U.ι ''ᵁ W)
  have hle : O ≤ V := f.preimage_mono (U.ι_image_le W)
  have he : V.ι ''ᵁ (V.ι ⁻¹ᵁ O) = O := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hle]
  have hi : IsIso (homOfLE (V.ι.image_preimage_le O)) := by
    rw [show homOfLE (V.ι.image_preimage_le O) = eqToHom he from Subsingleton.elim _ _]
    infer_instance
  exact Functor.map_isIso M.presheaf (homOfLE (V.ι.image_preimage_le O)).op

/-- The canonical open-base-change map is invertible. -/
theorem openBaseChangeMap_isIso : IsIso (openBaseChangeMap f U) := by
  have (M : X.Modules) : IsIso ((openBaseChangeMap f U).app M) := by
    rw [openBaseChangeMap_app]
    have := restrictedUnit_isIso f U M
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.BaseChangeMate.OpenPullbackSquare
