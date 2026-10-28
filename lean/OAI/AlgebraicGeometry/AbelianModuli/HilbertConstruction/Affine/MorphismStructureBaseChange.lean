import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.BaseChangeAffineRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms

/-! # Morphism Structure Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.MorphismStructureBaseChange

noncomputable section

/-! The actual structure-sheaf base-change map is an isomorphism for Cartesian squares whose two maps to the base are affine, over arbitrary schemes. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S X Y P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} [IsAffineHom f] [IsAffineHom g]
    (H : IsPullback a b f g)

theorem affineMorphism_structureBaseChange_isIso : IsIso (Structure.SheafBaseChange.structureBaseChangeMap H) := by
  apply Local.ModuleIsomorphisms.moduleMap_isIso_of_locally
  intro y
  obtain ⟨_, ⟨U : S.Opens, hU, rfl⟩, hy, _⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g y)) isOpen_univ
  exact ⟨g ⁻¹ᵁ U, hy, Structure.BaseChangeAffineRestriction.affineStructureBaseChange_pullback_preimage_isIso H U hU⟩

def affineMorphismStructureBaseChangeIso :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule X)) ≅
      (Scheme.Modules.pushforward b).obj (Line.Bundles.structureModule P) := by
  have := affineMorphism_structureBaseChange_isIso H
  exact asIso (Structure.SheafBaseChange.structureBaseChangeMap H)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.MorphismStructureBaseChange
