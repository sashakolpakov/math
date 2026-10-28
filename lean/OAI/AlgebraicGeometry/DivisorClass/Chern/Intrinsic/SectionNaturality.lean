import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.SectionCohomologyMap
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueDerivedNaturality

/-! # Section Naturality -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.SectionNaturality

noncomputable section

/-! The native section comparison respects actual cochain maps and the original flasque comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueDerivedNaturality.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}}

theorem abelianGammaSectionsIso_inv_naturality
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ} (f : K ⟶ L) :
    ((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSections X).mapHomologicalComplex (.up ℕ)).map f ≫ (GammaSectionsComparison.abelianGammaSectionsIso L).inv =
      (GammaSectionsComparison.abelianGammaSectionsIso K).inv ≫ FlasqueCechD.abelianDerivedSectionsMap f := by
  apply (GammaSectionsComparison.abelianGammaSectionsIso K).eq_inv_comp.mpr
  rw [← Category.assoc, ← GammaSectionsComparison.abelianGammaSectionsIso_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

theorem nativeSectionCohomologyMap_eq_flasque
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)
    (hK : ∀ q, IsFlasque (K.X q)) (he : ∀ q, K.ExactAt (q + 1)) (n : ℕ) :
    SectionCohomologyMap.nativeSectionCohomologyMap K he n =
      HomologicalComplex.homologyMap (GammaSectionsComparison.abelianGammaSectionsIso K).inv (n + 1) ≫
        (GammaSectionsComparison.nativeFlasqueCohomologyIso K hK he n).hom := by
  unfold SectionCohomologyMap.nativeSectionCohomologyMap SectionCohomologyMap.nativeInjectiveSectionCohomologyMap
  rw [GammaSectionsComparison.nativeFlasqueCohomologyIso_hom, ← Category.assoc, ← Category.assoc,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    abelianGammaSectionsIso_inv_naturality]

local instance nativeSectionNaturality_additive : (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).Additive :=
  (constantSheafΓAdj (Opens.grothendieckTopology X) AddCommGrpCat.{0}).right_adjoint_additive

theorem nativeInjectiveCohomologyIso_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (f : F ⟶ G)
    (r : (injectiveResolution F).cocomplex ⟶ (injectiveResolution G).cocomplex)
    (hr : (injectiveResolution F).ι.f 0 ≫ r.f 0 = f ≫ (injectiveResolution G).ι.f 0) (n : ℕ) :
    HomologicalComplex.homologyMap (FlasqueCechD.abelianDerivedSectionsMap r) (n + 1) ≫
        (GammaSectionsComparison.nativeInjectiveCohomologyIso G n).hom =
      (GammaSectionsComparison.nativeInjectiveCohomologyIso F n).hom ≫
        (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).map f := by
  let : (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).Additive := nativeSectionNaturality_additive
  have hd := InjectiveResolution.isoRightDerivedObj_inv_naturality f
    (injectiveResolution F) (injectiveResolution G) r hr (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X) (n + 1)
  change ((injectiveResolution F).isoRightDerivedObj (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X) (n + 1)).inv ≫
    ((SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).rightDerived (n + 1)).map f =
      HomologicalComplex.homologyMap (FlasqueCechD.abelianDerivedSectionsMap r) (n + 1) ≫
        ((injectiveResolution G).isoRightDerivedObj (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X) (n + 1)).inv at hd
  unfold GammaSectionsComparison.nativeInjectiveCohomologyIso
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← hd, Category.assoc]
  simp only [Category.assoc]
  congr 1
  ext x
  exact SheafCohomology.Cech.Compat.TopCat.Sheaf.H.addEquivRightDerivedGlobalSections_symm_naturality f (n + 1) x

theorem nativeInjectiveSectionCohomologyMap_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (f : F ⟶ G)
    (r : (injectiveResolution F).cocomplex ⟶ (injectiveResolution G).cocomplex)
    (hr : (injectiveResolution F).ι.f 0 ≫ r.f 0 = f ≫ (injectiveResolution G).ι.f 0) (n : ℕ) :
    HomologicalComplex.homologyMap (((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSections X).mapHomologicalComplex (.up ℕ)).map r) (n + 1) ≫
        SectionCohomologyMap.nativeInjectiveSectionCohomologyMap G n =
      SectionCohomologyMap.nativeInjectiveSectionCohomologyMap F n ≫
        (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).map f := by
  unfold SectionCohomologyMap.nativeInjectiveSectionCohomologyMap
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    abelianGammaSectionsIso_inv_naturality, HomologicalComplex.homologyMap_comp,
    Category.assoc, nativeInjectiveCohomologyIso_naturality f r hr, ← Category.assoc]

theorem nativeSectionCohomologyMap_naturality
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ} (f : K ⟶ L)
    (heK : ∀ q, K.ExactAt (q + 1)) (heL : ∀ q, L.ExactAt (q + 1)) (n : ℕ) :
    HomologicalComplex.homologyMap (((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSections X).mapHomologicalComplex (.up ℕ)).map f) (n + 1) ≫
        SectionCohomologyMap.nativeSectionCohomologyMap L heL n =
      SectionCohomologyMap.nativeSectionCohomologyMap K heK n ≫
        (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).map (HomologicalComplex.homologyMap f 0) := by
  let I := injectiveResolution (K.homology 0)
  let J := injectiveResolution (L.homology 0)
  let S := (CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSections X).mapHomologicalComplex (.up ℕ)
  let r := InjectiveResolution.desc (HomologicalComplex.homologyMap f 0) J I
  have hh : HomologicalComplex.homologyMap (S.map f) (n + 1) ≫
      HomologicalComplex.homologyMap (S.map (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift L heL J)) (n + 1) =
    HomologicalComplex.homologyMap (S.map (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift K heK I)) (n + 1) ≫
      HomologicalComplex.homologyMap (S.map r) (n + 1) := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← Functor.map_comp, ← Functor.map_comp]
    exact ((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSections X).mapHomotopy (HodgeConjecture.DegreeTwo.FlasqueDerivedNaturality.Constructions.resolutionLiftNaturalityHomotopy f heK heL I J)).homologyMap_eq (n + 1)
  unfold SectionCohomologyMap.nativeSectionCohomologyMap
  rw [← Category.assoc, hh, Category.assoc,
    nativeInjectiveSectionCohomologyMap_naturality _ _ (InjectiveResolution.desc_commutes_zero _ _ _),
    ← Category.assoc]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.SectionNaturality
