import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.SectionNaturality
import OAI.AlgebraicGeometry.DivisorClass.Chern.AugmentedCochainZeroIso

/-! # Augmentation Naturality -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.AugmentationNaturality

noncomputable section

/-! The native cohomology map intertwines original coefficient sheaves through actual augmentation squares. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section ZeroNaturality

variable {C : Type*} [Category C] [Abelian C]
  {K L : CochainComplex C ℕ} {F G : C}

theorem cochainAugmentationZeroIso_naturality (f : K ⟶ L) (u : F ⟶ G)
    (eF : F ≅ K.homology 0) (eG : G ≅ L.homology 0) (i : F ⟶ K.X 0) (j : G ⟶ L.X 0)
    (hi : eF.hom ≫ (HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K).f 0 = i)
    (hj : eG.hom ≫ (HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation L).f 0 = j) (hf : i ≫ f.f 0 = u ≫ j) :
    eF.hom ≫ HomologicalComplex.homologyMap f 0 = u ≫ eG.hom := by
  have : Mono ((HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation L).f 0) := HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.cochainZeroHomologyAugmentation_zero_mono L
  apply (cancel_mono ((HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation L).f 0)).mp
  have hc : HomologicalComplex.homologyMap f 0 ≫ (HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation L).f 0 =
      (HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K).f 0 ≫ f.f 0 := by
    simpa only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero] using
      congrArg (fun g => g.f 0) (HodgeConjecture.DegreeTwo.ThomResolutionDiagram.Constructions.cochainZeroHomologyAugmentation_naturality f)
  rw [Category.assoc, hc, ← Category.assoc, hi, hf, Category.assoc, hj]

end ZeroNaturality

variable {X : TopCat.{0}}

def nativeSectionCohomologyMapOfZero (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)
    (he : ∀ q, K.ExactAt (q + 1)) {F : TopCat.Sheaf AddCommGrpCat.{0} X}
    (e : F ≅ K.homology 0) (n : ℕ) :
    (CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex K).homology (n + 1) ⟶
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).obj F :=
  SectionCohomologyMap.nativeSectionCohomologyMap K he n ≫
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).map e.inv

theorem nativeSectionCohomologyMapOfZero_naturality
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ} (f : K ⟶ L)
    (heK : ∀ q, K.ExactAt (q + 1)) (heL : ∀ q, L.ExactAt (q + 1))
    {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (u : F ⟶ G)
    (eF : F ≅ K.homology 0) (eG : G ≅ L.homology 0)
    (hzero : eF.hom ≫ HomologicalComplex.homologyMap f 0 = u ≫ eG.hom) (n : ℕ) :
    HomologicalComplex.homologyMap (((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSections X).mapHomologicalComplex (.up ℕ)).map f) (n + 1) ≫
        nativeSectionCohomologyMapOfZero L heL eG n =
      nativeSectionCohomologyMapOfZero K heK eF n ≫
        (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).map u := by
  have hi : HomologicalComplex.homologyMap f 0 ≫ eG.inv = eF.inv ≫ u := by
    apply eF.eq_inv_comp.mpr
    rw [← Category.assoc, hzero, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  unfold nativeSectionCohomologyMapOfZero
  rw [← Category.assoc, SectionNaturality.nativeSectionCohomologyMap_naturality, Category.assoc,
    ← Functor.map_comp, hi, Functor.map_comp, ← Category.assoc]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.AugmentationNaturality
