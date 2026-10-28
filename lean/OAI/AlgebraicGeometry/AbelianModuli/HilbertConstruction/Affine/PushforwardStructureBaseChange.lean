import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SourceStructureBaseChange

/-! # Pushforward Structure Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardStructureBaseChange

noncomputable section

/-! Formation of the structure-sheaf pushforward along an affine morphism commutes with arbitrary scheme base change, via the canonical map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S X Y P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} [IsAffineHom f] (H : IsPullback a b f g)

theorem affinePushforward_structureBaseChange_preimage_isIso (U : S.Opens) (hU : IsAffineOpen U) :
    IsIso ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).map (Structure.SheafBaseChange.structureBaseChangeMap H)) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine (f ⁻¹ᵁ U).toScheme := hU.preimage f
  let Ho := (isPullback_morphismRestrict f U).flip
  let Hl := Cartesian.OpenRestriction.restrictedCartesianSquare H U
  let Hb := (isPullback_morphismRestrict b (g ⁻¹ᵁ U)).flip
  have : IsIso (Structure.SheafBaseChange.structureBaseChangeMap Ho) := Open.CanonicalBaseChange.openStructureBaseChange_isIso f U
  have : IsIso (Structure.SheafBaseChange.structureBaseChangeMap Hl) := SourceStructureBaseChange.affineSource_structureBaseChange_isIso Hl
  have houter : IsIso (Structure.SheafBaseChange.structureBaseChangeMap (Hl.paste_horiz Ho)) := by
    rw [← Structure.BaseChangeComposition.structureBaseChangeMap_paste Ho Hl]
    infer_instance
  have houter' : IsIso (Structure.SheafBaseChange.structureBaseChangeMap (Hb.paste_horiz H)) :=
    (Structure.BaseChangeAffineRestriction.structureBaseChange_isIso_congr (Hl.paste_horiz Ho) (Hb.paste_horiz H)
      (Cartesian.OpenRestriction.restrictedCartesianFirst_comp_ι H U) (morphismRestrict_ι g U)).mp houter
  have : IsIso (Structure.SheafBaseChange.structureBaseChangeMap Hb) := Open.CanonicalBaseChange.openStructureBaseChange_isIso b (g ⁻¹ᵁ U)
  have hc : IsIso
      ((Scheme.Modules.pullbackComp (g ⁻¹ᵁ U).ι g).inv.app
          ((Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule X)) ≫
        (Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).map (Structure.SheafBaseChange.structureBaseChangeMap H) ≫
          Structure.SheafBaseChange.structureBaseChangeMap Hb) := by
    rw [Structure.BaseChangeComposition.structureBaseChangeMap_paste H Hb]
    exact houter'
  have hm : IsIso
      ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).map (Structure.SheafBaseChange.structureBaseChangeMap H) ≫
        Structure.SheafBaseChange.structureBaseChangeMap Hb) := (isIso_comp_left_iff _ _).mp hc
  exact (isIso_comp_right_iff _ _).mp hm

theorem affinePushforward_structureBaseChange_isIso : IsIso (Structure.SheafBaseChange.structureBaseChangeMap H) := by
  apply Local.ModuleIsomorphisms.moduleMap_isIso_of_locally
  intro y
  obtain ⟨_, ⟨U : S.Opens, hU, rfl⟩, hy, _⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g y)) isOpen_univ
  exact ⟨g ⁻¹ᵁ U, hy, affinePushforward_structureBaseChange_preimage_isIso H U hU⟩

def affinePushforwardStructureBaseChangeIso :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule X)) ≅
      (Scheme.Modules.pushforward b).obj (Line.Bundles.structureModule P) := by
  have := affinePushforward_structureBaseChange_isIso H
  exact asIso (Structure.SheafBaseChange.structureBaseChangeMap H)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardStructureBaseChange
