import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.CanonicalBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.StructureSheafBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.BaseChangeComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.OpenRestriction

/-! # Base Change Affine Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.BaseChangeAffineRestriction

noncomputable section

/-! For affine morphisms, the actual structure base-change map is invertible after pullback to every inverse image of an affine base open. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem structureBaseChange_isIso_congr {S X Y P : Scheme.{u}}
    {a a' : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g g' : Y ⟶ S}
    (H : IsPullback a b f g) (H' : IsPullback a' b f g') (ha : a = a') (hg : g = g') :
    IsIso (SheafBaseChange.structureBaseChangeMap H) ↔ IsIso (SheafBaseChange.structureBaseChangeMap H') := by
  subst a'
  subst g'
  rfl

theorem affineStructureBaseChange_pullback_preimage_isIso {S X Y P : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    [IsAffineHom f] [IsAffineHom g] (H : IsPullback a b f g)
    (U : S.Opens) (hU : IsAffineOpen U) :
    IsIso ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).map (SheafBaseChange.structureBaseChangeMap H)) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine (f ⁻¹ᵁ U).toScheme := hU.preimage f
  have : IsAffine (g ⁻¹ᵁ U).toScheme := hU.preimage g
  let Ho := (isPullback_morphismRestrict f U).flip
  let Hl := Cartesian.OpenRestriction.restrictedCartesianSquare H U
  let Hb := (isPullback_morphismRestrict b (g ⁻¹ᵁ U)).flip
  have : IsIso (SheafBaseChange.structureBaseChangeMap Ho) := Open.CanonicalBaseChange.openStructureBaseChange_isIso f U
  have : IsIso (SheafBaseChange.structureBaseChangeMap Hl) := Affine.StructureSheafBaseChange.affineStructureBaseChangeMap_isIso Hl
  have houter : IsIso (SheafBaseChange.structureBaseChangeMap (Hl.paste_horiz Ho)) := by
    rw [← BaseChangeComposition.structureBaseChangeMap_paste Ho Hl]
    infer_instance
  have houter' : IsIso (SheafBaseChange.structureBaseChangeMap (Hb.paste_horiz H)) :=
    (structureBaseChange_isIso_congr (Hl.paste_horiz Ho) (Hb.paste_horiz H)
      (Cartesian.OpenRestriction.restrictedCartesianFirst_comp_ι H U) (morphismRestrict_ι g U)).mp houter
  have : IsIso (SheafBaseChange.structureBaseChangeMap Hb) := Open.CanonicalBaseChange.openStructureBaseChange_isIso b (g ⁻¹ᵁ U)
  have hc : IsIso
      ((Scheme.Modules.pullbackComp (g ⁻¹ᵁ U).ι g).inv.app
          ((Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule X)) ≫
        (Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).map (SheafBaseChange.structureBaseChangeMap H) ≫
          SheafBaseChange.structureBaseChangeMap Hb) := by
    rw [BaseChangeComposition.structureBaseChangeMap_paste H Hb]
    exact houter'
  have hm : IsIso
      ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).map (SheafBaseChange.structureBaseChangeMap H) ≫
        SheafBaseChange.structureBaseChangeMap Hb) := (isIso_comp_left_iff _ _).mp hc
  exact (isIso_comp_right_iff _ _).mp hm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.BaseChangeAffineRestriction
