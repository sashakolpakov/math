import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.AnnihilatorRepresentation

/-! # Ordinary Opposite Models -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryOppositeModels.Construction

noncomputable section

/-!
The scheme-theoretic opposite annihilator in a split ordinary block is
the actual Cartier group of the complementary factor. The comparison is
constructed from restriction maps, so it also respects the group law.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {R : CommRingCat.{u}} {B G H : Grp (Over (Spec R))}
variable (e : B ≅ G ⊗ H) (P : CartierModel.Construction.CartierCoordinates R B)
variable (Q : CartierModel.Construction.CartierCoordinates R G) (V : CartierModel.Construction.CartierCoordinates R H)

def splitOppositeRestriction :
    P.annihilatorGroup Q (AnnihilatorSheaf.Construction.splitFirstInclusion G H ≫ e.inv) ⟶ V.dualGroup :=
  P.annihilatorInclusion Q (AnnihilatorSheaf.Construction.splitFirstInclusion G H ≫ e.inv) ≫
    P.restriction V (AnnihilatorSheaf.Construction.splitSecondInclusion G H ≫ e.inv)

theorem splitOppositeRestriction_characterMap :
    (BaseChange.Construction.fppfPoints (Spec R)).map (splitOppositeRestriction e P Q V).hom.hom ≫
      V.characterIso.hom =
        (P.annihilatorSheafIso Q (AnnihilatorSheaf.Construction.splitFirstInclusion G H ≫ e.inv)).hom ≫
          (AnnihilatorSheaf.Construction.annihilatorSheafIsoOfSplitting B G H e).hom := by
  let F := BaseChange.Construction.fppfPoints (Spec R)
  let i := AnnihilatorSheaf.Construction.splitFirstInclusion G H ≫ e.inv
  let j := AnnihilatorSheaf.Construction.splitSecondInclusion G H ≫ e.inv
  let a := (P.annihilatorInclusion Q i).hom.hom
  let d := (P.restriction V j).hom.hom
  let χ : F.obj P.dualGroup.X ⟶ CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec R) B :=
    P.characterIso.hom
  let ψ : F.obj V.dualGroup.X ⟶ CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec R) H :=
    V.characterIso.hom
  let r := CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction j
  have hd : F.map d ≫ ψ = χ ≫ r := P.restriction_characterIso V j
  have ha : (P.annihilatorSheafIso Q i).hom ≫ equalizer.ι _ _ = F.map a ≫ χ :=
    P.annihilatorSheafIso_inclusion Q i
  change F.map (a ≫ d) ≫ ψ = _
  calc
    F.map (a ≫ d) ≫ ψ = F.map a ≫ F.map d ≫ ψ := by rw [Functor.map_comp, Category.assoc]
    _ = F.map a ≫ χ ≫ r := congrArg (fun f => F.map a ≫ f) hd
    _ = (P.annihilatorSheafIso Q i).hom ≫ equalizer.ι _ _ ≫ r :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ r) ha.symm).trans (Category.assoc _ _ _))
    _ = (P.annihilatorSheafIso Q i).hom ≫
        (AnnihilatorSheaf.Construction.annihilatorSheafIsoOfSplitting B G H e).hom :=
      congrArg (fun f => (P.annihilatorSheafIso Q i).hom ≫ f)
        (AnnihilatorSheaf.Construction.annihilatorSheafIsoOfSplitting_hom B G H e).symm

instance splitOppositeRestriction_isIso : IsIso (splitOppositeRestriction e P Q V).hom.hom := by
  let f := (splitOppositeRestriction e P Q V).hom.hom
  let F := BaseChange.Construction.fppfPoints (Spec R)
  let ψ : F.obj V.dualGroup.X ⟶ CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec R) H :=
    V.characterIso.hom
  have : IsIso ψ := inferInstanceAs (IsIso V.characterIso.hom)
  have : IsIso (F.map f ≫ ψ) := (congrArg IsIso
    (splitOppositeRestriction_characterMap e P Q V)).mpr inferInstance
  have : IsIso (F.map f) := IsIso.of_isIso_comp_right (F.map f) ψ
  exact isIso_of_reflects_iso f F

/-- The ordinary opposite kernel is identified as an actual group scheme,
not only through its geometric points or its underlying scheme. -/
def splitOppositeGroupIso :
    P.annihilatorGroup Q (AnnihilatorSheaf.Construction.splitFirstInclusion G H ≫ e.inv) ≅ V.dualGroup :=
  Grp.mkIso (asIso (splitOppositeRestriction e P Q V).hom.hom)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryOppositeModels.Construction
