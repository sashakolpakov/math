import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.AnnihilatorRepresentation

/-! # Cartier Functoriality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-!
Native Cartier restriction preserves identities and reverses composition.
Coordinate changes therefore give actual dual-group isomorphisms, with
the restriction square needed to transport opposite annihilators.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {R : CommRingCat.{u}} {G H J : Grp (Over (Spec R))}

theorem CartierModel.Construction.CartierCoordinates.restriction_id (P : CartierModel.Construction.CartierCoordinates R G) : P.restriction P (𝟙 G) = 𝟙 P.dualGroup := by
  apply Grp.hom_ext
  apply (BaseChange.Construction.fppfPoints (Spec R)).map_injective
  apply (cancel_mono P.characterIso.hom).mp
  exact (P.restriction_characterIso P (𝟙 G)).trans
    (((congrArg (fun z => P.characterIso.hom ≫ z) (AnnihilatorSheaf.Construction.characterRestriction_id G)).trans
      (Category.comp_id P.characterIso.hom)).trans
      ((congrArg (fun z => z ≫ P.characterIso.hom)
        ((BaseChange.Construction.fppfPoints (Spec R)).map_id P.dualGroup.X)).trans
          (Category.id_comp P.characterIso.hom)).symm)

theorem CartierModel.Construction.CartierCoordinates.restriction_comp (P : CartierModel.Construction.CartierCoordinates R G) (Q : CartierModel.Construction.CartierCoordinates R H)
    (V : CartierModel.Construction.CartierCoordinates R J) (i : H ⟶ G) (j : J ⟶ H) :
    P.restriction Q i ≫ Q.restriction V j = P.restriction V (j ≫ i) := by
  apply Grp.hom_ext
  change (P.restriction Q i).hom.hom ≫ (Q.restriction V j).hom.hom = _
  apply (BaseChange.Construction.fppfPoints (Spec R)).map_injective
  apply (cancel_mono V.characterIso.hom).mp
  let F := BaseChange.Construction.fppfPoints (Spec R)
  let a : F.obj P.dualScheme ⟶ F.obj Q.dualScheme := F.map (P.restriction Q i).hom.hom
  let b : F.obj Q.dualScheme ⟶ F.obj V.dualScheme := F.map (Q.restriction V j).hom.hom
  let c := CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction i
  let d := CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction j
  exact (congrArg (fun z => z ≫ V.characterIso.hom) (F.map_comp _ _)).trans
    ((Category.assoc a b V.characterIso.hom).trans
      ((congrArg (fun z => a ≫ z) (Q.restriction_characterIso V j)).trans
        ((Category.assoc a Q.characterIso.hom d).symm.trans
          ((congrArg (fun z => z ≫ d) (P.restriction_characterIso Q i)).trans
            ((Category.assoc P.characterIso.hom c d).trans
              ((congrArg (fun z => P.characterIso.hom ≫ z) (AnnihilatorSheaf.Construction.characterRestriction_comp j i)).trans
                (P.restriction_characterIso V (j ≫ i)).symm))))))

def CartierModel.Construction.CartierCoordinates.dualIso (P : CartierModel.Construction.CartierCoordinates R G) (Q : CartierModel.Construction.CartierCoordinates R H) (e : G ≅ H) :
    Q.dualGroup ≅ P.dualGroup where
  hom := Q.restriction P e.hom
  inv := P.restriction Q e.inv
  hom_inv_id := by rw [CartierModel.Construction.CartierCoordinates.restriction_comp, e.inv_hom_id, CartierModel.Construction.CartierCoordinates.restriction_id]
  inv_hom_id := by rw [CartierModel.Construction.CartierCoordinates.restriction_comp, e.hom_inv_id, CartierModel.Construction.CartierCoordinates.restriction_id]

variable {G' H' : Grp (Over (Spec R))}
variable (P : CartierModel.Construction.CartierCoordinates R G) (Q : CartierModel.Construction.CartierCoordinates R H)
variable (P' : CartierModel.Construction.CartierCoordinates R G') (Q' : CartierModel.Construction.CartierCoordinates R H')
variable (i : H ⟶ G) (i' : H' ⟶ G') (eG : G ≅ G') (eH : H ≅ H')
variable (hsquare : i ≫ eG.hom = eH.hom ≫ i')

include hsquare in
theorem CartierModel.Construction.CartierCoordinates.dualIso_restriction :
    (P.dualIso P' eG).hom ≫ P.restriction Q i =
      P'.restriction Q' i' ≫ (Q.dualIso Q' eH).hom := by
  change P'.restriction P eG.hom ≫ P.restriction Q i =
    P'.restriction Q' i' ≫ Q'.restriction Q eH.hom
  rw [CartierModel.Construction.CartierCoordinates.restriction_comp, CartierModel.Construction.CartierCoordinates.restriction_comp, hsquare]

/-- A coordinate change transports the complete actual opposite
annihilator scheme, with no reducedness assumption. -/
def CartierModel.Construction.CartierCoordinates.annihilatorIso : (P'.annihilatorGroup Q' i').X ≅ (P.annihilatorGroup Q i).X :=
  P'.annihilatorEqualizerIso Q' i' ≪≫
    CategoryTheory.Limits.HasLimit.isoOfNatIso
      (CategoryTheory.Limits.parallelPairIso _ _ _ _
        ((Grp.forget (Over (Spec R))).mapIso (P.dualIso P' eG))
        ((Grp.forget (Over (Spec R))).mapIso (Q.dualIso Q' eH))
        (congrArg (fun f => f.hom.hom) (P.dualIso_restriction Q P' Q' i i' eG eH hsquare)).symm
        (by
          change (1 : P'.dualGroup.X ⟶ Q'.dualGroup.X) ≫ (Q.dualIso Q' eH).hom.hom.hom =
            (P.dualIso P' eG).hom.hom.hom ≫ (1 : P.dualGroup.X ⟶ Q.dualGroup.X)
          exact (MonObj.one_comp _).trans (MonObj.comp_one _).symm)) ≪≫
    (P.annihilatorEqualizerIso Q i).symm

theorem CartierModel.Construction.CartierCoordinates.annihilatorIso_inclusion :
    (P.annihilatorIso Q P' Q' i i' eG eH hsquare).hom ≫ (P.annihilatorInclusion Q i).hom.hom =
      (P'.annihilatorInclusion Q' i').hom.hom ≫ (P.dualIso P' eG).hom.hom.hom := by
  let w := CategoryTheory.Limits.parallelPairIso
    (P'.restriction Q' i').hom.hom (1 : P'.dualGroup.X ⟶ Q'.dualGroup.X)
    (P.restriction Q i).hom.hom (1 : P.dualGroup.X ⟶ Q.dualGroup.X)
    ((Grp.forget (Over (Spec R))).mapIso (P.dualIso P' eG))
    ((Grp.forget (Over (Spec R))).mapIso (Q.dualIso Q' eH))
    (congrArg (fun f => f.hom.hom) (P.dualIso_restriction Q P' Q' i i' eG eH hsquare)).symm
    (by
      change (1 : P'.dualGroup.X ⟶ Q'.dualGroup.X) ≫ (Q.dualIso Q' eH).hom.hom.hom =
        (P.dualIso P' eG).hom.hom.hom ≫ (1 : P.dualGroup.X ⟶ Q.dualGroup.X)
      exact (MonObj.one_comp _).trans (MonObj.comp_one _).symm)
  have hw := CategoryTheory.Limits.HasLimit.isoOfNatIso_hom_π w CategoryTheory.Limits.WalkingParallelPair.zero
  change (CategoryTheory.Limits.HasLimit.isoOfNatIso w).hom ≫
      CategoryTheory.Limits.equalizer.ι (P.restriction Q i).hom.hom (1 : P.dualGroup.X ⟶ Q.dualGroup.X) =
    CategoryTheory.Limits.equalizer.ι (P'.restriction Q' i').hom.hom (1 : P'.dualGroup.X ⟶ Q'.dualGroup.X) ≫
      (P.dualIso P' eG).hom.hom.hom at hw
  have hi : (P.annihilatorEqualizerIso Q i).inv ≫ (P.annihilatorInclusion Q i).hom.hom =
      CategoryTheory.Limits.equalizer.ι (P.restriction Q i).hom.hom (1 : P.dualGroup.X ⟶ Q.dualGroup.X) := by
    rw [← P.annihilatorEqualizerIso_inclusion Q i, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change ((P'.annihilatorEqualizerIso Q' i').hom ≫
    (CategoryTheory.Limits.HasLimit.isoOfNatIso w).hom ≫ (P.annihilatorEqualizerIso Q i).inv) ≫ _ = _
  rw [Category.assoc, Category.assoc, hi, hw, ← Category.assoc,
    P'.annihilatorEqualizerIso_inclusion Q' i']

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
