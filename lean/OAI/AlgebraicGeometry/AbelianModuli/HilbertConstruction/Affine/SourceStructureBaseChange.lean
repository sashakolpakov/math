import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.MorphismStructureBaseChange

/-! # Source Structure Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SourceStructureBaseChange

noncomputable section

/-! If the original source and base are affine, the canonical structure base-change map is invertible for an arbitrary new base scheme. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S X Y P : Scheme.{u}} [IsAffine S] [IsAffine X]
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S} (H : IsPullback a b f g)

theorem affineSource_structureBaseChange_isIso : IsIso (Structure.SheafBaseChange.structureBaseChangeMap H) := by
  apply Local.ModuleIsomorphisms.moduleMap_isIso_of_locally
  intro y
  obtain ⟨_, ⟨V : Y.Opens, hV, rfl⟩, hy, _⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have : IsAffine V.toScheme := hV
  let Hb := (isPullback_morphismRestrict b V).flip
  have houter : IsIso (Structure.SheafBaseChange.structureBaseChangeMap (Hb.paste_horiz H)) :=
    StructureSheafBaseChange.affineStructureBaseChangeMap_isIso (Hb.paste_horiz H)
  have : IsIso (Structure.SheafBaseChange.structureBaseChangeMap Hb) := Open.CanonicalBaseChange.openStructureBaseChange_isIso b V
  have hc : IsIso
      ((Scheme.Modules.pullbackComp V.ι g).inv.app
          ((Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule X)) ≫
        (Scheme.Modules.pullback V.ι).map (Structure.SheafBaseChange.structureBaseChangeMap H) ≫
          Structure.SheafBaseChange.structureBaseChangeMap Hb) := by
    rw [Structure.BaseChangeComposition.structureBaseChangeMap_paste H Hb]
    exact houter
  have hm : IsIso
      ((Scheme.Modules.pullback V.ι).map (Structure.SheafBaseChange.structureBaseChangeMap H) ≫
        Structure.SheafBaseChange.structureBaseChangeMap Hb) := (isIso_comp_left_iff _ _).mp hc
  exact ⟨V, hy, (isIso_comp_right_iff _ _).mp hm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SourceStructureBaseChange
