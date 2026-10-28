import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GroupFieldBaseChange

/-! # Field Base Change Maps -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FieldBaseChangeMaps.Construction

noncomputable section

/-! Scalar extension of the actual morphisms and closed inclusions in
a finite-group tower. The maps retain the native base-change square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']
variable {G H : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k}
variable (a : G.scheme ⟶ H.scheme) [IsMonHom a]

def finiteGroupFieldBaseChangeMap :
    Grp.mk (GroupFieldBaseChange.Construction.finiteGroupFieldBaseChange (k' := k') G).scheme ⟶
      Grp.mk (GroupFieldBaseChange.Construction.finiteGroupFieldBaseChange (k' := k') H).scheme :=
  (GroupFieldBaseChange.Construction.finiteGroupFieldBaseChangeGroupIso (k' := k') G).inv ≫
    (Over.pullback (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k'))).mapGrp.map (Grp.ofHom a) ≫
      (GroupFieldBaseChange.Construction.finiteGroupFieldBaseChangeGroupIso (k' := k') H).hom

theorem finiteGroupFieldBaseChangeMap_square :
    (GroupFieldBaseChange.Construction.finiteGroupFieldBaseChangeGroupIso (k' := k') G).hom ≫ finiteGroupFieldBaseChangeMap (k' := k') a =
      (Over.pullback (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k'))).mapGrp.map (Grp.ofHom a) ≫
        (GroupFieldBaseChange.Construction.finiteGroupFieldBaseChangeGroupIso (k' := k') H).hom := by
  change (GroupFieldBaseChange.Construction.finiteGroupFieldBaseChangeGroupIso (k' := k') G).hom ≫
    ((GroupFieldBaseChange.Construction.finiteGroupFieldBaseChangeGroupIso (k' := k') G).inv ≫ _ ≫ _) = _
  rw [Iso.hom_inv_id_assoc]

instance finiteGroupFieldBaseChangeMap_closed [IsClosedImmersion a.left] :
    IsClosedImmersion (finiteGroupFieldBaseChangeMap (k' := k') a).hom.hom.left := by
  let F := Over.pullback (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k'))
  let eG := GroupFieldBaseChange.Construction.finiteGroupFieldBaseChangeGroupIso (k' := k') G
  let eH := GroupFieldBaseChange.Construction.finiteGroupFieldBaseChangeGroupIso (k' := k') H
  let b := F.mapGrp.map (Grp.ofHom a)
  have : IsClosedImmersion b.hom.hom.left :=
    MorphismProperty.overPullbackMap (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k')) a inferInstance
  have : IsIso eG.inv.hom.hom.left :=
    inferInstanceAs (IsIso (((Grp.forget _) ⋙ Over.forget _).map eG.inv))
  have : IsIso eH.hom.hom.hom.left :=
    inferInstanceAs (IsIso (((Grp.forget _) ⋙ Over.forget _).map eH.hom))
  change IsClosedImmersion (eG.inv.hom.hom.left ≫ b.hom.hom.left ≫ eH.hom.hom.hom.left)
  infer_instance

def finiteGroupNativeBaseChangeIso (G : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k) :
    (Over.pullback (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k'))).obj G.scheme ≅
      (GroupFieldBaseChange.Construction.finiteGroupFieldBaseChange (k' := k') G).scheme :=
  GroupFieldBaseChange.Construction.finiteGroupFieldBaseChangeSchemeIso G

def finiteGroupFieldBaseChangeSchemeMap :
    (GroupFieldBaseChange.Construction.finiteGroupFieldBaseChange (k' := k') G).scheme ⟶
      (GroupFieldBaseChange.Construction.finiteGroupFieldBaseChange (k' := k') H).scheme :=
  (finiteGroupNativeBaseChangeIso (k' := k') G).inv ≫
    (Over.pullback (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k'))).map a ≫
      (finiteGroupNativeBaseChangeIso (k' := k') H).hom

theorem finiteGroupFieldBaseChangeSchemeMap_eq :
    finiteGroupFieldBaseChangeSchemeMap (k' := k') a =
      (finiteGroupFieldBaseChangeMap (k' := k') a).hom.hom := rfl

instance finiteGroupFieldBaseChangeSchemeMap_isMonHom :
    IsMonHom (finiteGroupFieldBaseChangeSchemeMap (k' := k') a) := by
  rw [finiteGroupFieldBaseChangeSchemeMap_eq]
  infer_instance

instance finiteGroupFieldBaseChangeSchemeMap_closed [IsClosedImmersion a.left] :
    IsClosedImmersion (finiteGroupFieldBaseChangeSchemeMap (k' := k') a).left := by
  rw [finiteGroupFieldBaseChangeSchemeMap_eq]
  infer_instance

omit [IsMonHom a] in
theorem finiteGroupFieldBaseChangeSchemeMap_square :
    (finiteGroupNativeBaseChangeIso (k' := k') G).hom ≫ finiteGroupFieldBaseChangeSchemeMap (k' := k') a =
      (Over.pullback (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k'))).map a ≫
        (finiteGroupNativeBaseChangeIso (k' := k') H).hom := by
  change (finiteGroupNativeBaseChangeIso (k' := k') G).hom ≫
    ((finiteGroupNativeBaseChangeIso (k' := k') G).inv ≫ _ ≫ _) = _
  exact Iso.hom_inv_id_assoc _ _

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FieldBaseChangeMaps.Construction
