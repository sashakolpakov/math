import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.MorphismSectionEquivalence

/-! # Morphism Section Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.MorphismSectionNaturality

noncomputable section

/-! The total-product description of family morphisms commutes with every actual geometric parameter base change. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem familyTotalSpaceMap_swap
    {S : Scheme.{u}} {U T : Over S} (c : U ⟶ T) (A : Over S) :
    ((MorphismSectionEquivalence.familyTotalSpaceFunctor A).map c).left ≫ (pullbackSymmetry T.hom A.hom).hom =
      (pullbackSymmetry U.hom A.hom).hom ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap c A := by
  let k : pullback U.hom A.hom ⟶ pullback T.hom A.hom := ((MorphismSectionEquivalence.familyTotalSpaceFunctor A).map c).left
  let r : pullback A.hom U.hom ⟶ pullback A.hom T.hom := Single.ParameterBaseChange.singleParameterBaseChangeMap c A
  change k ≫ (pullbackSymmetry T.hom A.hom).hom = (pullbackSymmetry U.hom A.hom).hom ≫ r
  have hf : k ≫ pullback.fst T.hom A.hom =
      pullback.fst U.hom A.hom ≫ c.left := pullback.lift_fst _ _ _
  have hs : k ≫ pullback.snd T.hom A.hom =
      pullback.snd U.hom A.hom := pullback.lift_snd _ _ _
  have hr : r ≫ pullback.fst A.hom T.hom = pullback.fst A.hom U.hom := Single.ParameterBaseChange.singleParameterBaseChangeMap_comp c A
  have ht : r ≫ pullback.snd A.hom T.hom = pullback.snd A.hom U.hom ≫ c.left :=
    Single.ParameterFunctoriality.singleParameterBaseChangeMap_over c A
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSymmetry_hom_comp_fst, hs, Category.assoc,
      hr, pullbackSymmetry_hom_comp_fst]
  · rw [Category.assoc, pullbackSymmetry_hom_comp_snd, hf, Category.assoc,
      ht, ← Category.assoc, pullbackSymmetry_hom_comp_snd]

theorem familyMorphismSectionEquiv_natural
    {S : Scheme.{u}} (A B : Over S) {U T : Over S} (c : U ⟶ T)
    (p : (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B) :
    (MorphismSectionEquivalence.familyTotalSpaceFunctor A).map c ≫ MorphismSectionEquivalence.familyMorphismSectionEquiv A B T p =
      MorphismSectionEquivalence.familyMorphismSectionEquiv A B U (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c p) := by
  have h : Single.ParameterBaseChange.singleParameterBaseChangeMap c A ≫ p.left ≫ pullback.fst B.hom T.hom =
      (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c p).left ≫ pullback.fst B.hom U.hom := by
    rw [← Category.assoc, ← Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange_comp, Category.assoc,
      Single.ParameterBaseChange.singleParameterBaseChangeMap_comp]
  apply Over.OverMorphism.ext
  rw [Over.comp_left, MorphismSectionEquivalence.familyMorphismSectionEquiv_left, MorphismSectionEquivalence.familyMorphismSectionEquiv_left]
  let k : pullback U.hom A.hom ⟶ pullback T.hom A.hom := ((MorphismSectionEquivalence.familyTotalSpaceFunctor A).map c).left
  exact (Category.assoc k (pullbackSymmetry T.hom A.hom).hom (p.left ≫ pullback.fst B.hom T.hom)).symm.trans
    ((congrArg (fun r : pullback U.hom A.hom ⟶ pullback A.hom T.hom => r ≫ p.left ≫ pullback.fst B.hom T.hom)
      (familyTotalSpaceMap_swap c A)).trans
      ((Category.assoc (pullbackSymmetry U.hom A.hom).hom (Single.ParameterBaseChange.singleParameterBaseChangeMap c A)
        (p.left ≫ pullback.fst B.hom T.hom)).trans
        (congrArg (fun q => (pullbackSymmetry U.hom A.hom).hom ≫ q) h)))

def familyMorphismSectionIso {S : Scheme.{u}} (A B : Over S) :
    Geometric.MorphismFunctor.geometricFamilyMorphismFunctor A B ≅ (MorphismSectionEquivalence.familyTotalSpaceFunctor A).op ⋙ yoneda.obj B :=
  NatIso.ofComponents (fun T => (MorphismSectionEquivalence.familyMorphismSectionEquiv A B T.unop).toIso) (by
    intro T U c
    apply ConcreteCategory.hom_ext
    intro p
    exact (familyMorphismSectionEquiv_natural A B c.unop p).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.MorphismSectionNaturality
