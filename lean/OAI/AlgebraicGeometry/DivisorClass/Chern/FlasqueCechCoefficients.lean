import OAI.AlgebraicGeometry.DivisorClass.Chern.GammaSectionsComparison

/-! # Flasque Cech Coefficients -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.FlasqueCechCoefficients

noncomputable section

/-! Coefficient naturality of the comparison through an actual flasque resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)
  {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ}
  {F G : TopCat.Sheaf AddCommGrpCat.{0} X}

theorem abelianCechVerticalEdge_coefficients (f : F ⟶ G) (a : G ⟶ K.X 0)
    (ha : a ≫ K.d 0 1 = 0) (hfa : (f ≫ a) ≫ K.d 0 1 = 0) :
    (CategoryTheory.cechComplexFunctor U).map f.hom ≫ FlasqueCechD.abelianCechVerticalEdge U a ha =
      FlasqueCechD.abelianCechVerticalEdge U (f ≫ a) hfa := by
  apply HomologicalComplex.Hom.ext
  funext p
  rw [HomologicalComplex.comp_f, FlasqueCechD.abelianCechVerticalEdge_f, FlasqueCechD.abelianCechVerticalEdge_f,
    ← Category.assoc]
  congr 1
  change ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).map f).f p ≫ ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).map a).f p =
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).map (f ≫ a)).f p
  rw [Functor.map_comp, HomologicalComplex.comp_f]

theorem abelianCechFlasqueComparison_coefficients (hK : ∀ q, IsFlasque (K.X q))
    (f : F ⟶ G) (a : G ⟶ K.X 0) (ha : a ≫ K.d 0 1 = 0)
    (hfa : (f ≫ a) ≫ K.d 0 1 = 0) (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    HomologicalComplex.homologyMap ((CategoryTheory.cechComplexFunctor U).map f.hom) (n + 1) ≫
        FlasqueCechD.abelianCechFlasqueComparison U hK a ha hU n =
      FlasqueCechD.abelianCechFlasqueComparison U hK (f ≫ a) hfa hU n := by
  unfold FlasqueCechD.abelianCechFlasqueComparison
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    abelianCechVerticalEdge_coefficients U f a ha hfa]

theorem nativeFlasqueCohomologyIsoOfZero_cech
    (hK : ∀ q, IsFlasque (K.X q)) (he : ∀ q, K.ExactAt (q + 1))
    (e : F ≅ K.homology 0)
    (ha : (e.hom ≫ (HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K).f 0) ≫ K.d 0 1 = 0)
    (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    FlasqueCechD.abelianCechFlasqueComparison U hK (e.hom ≫ (HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K).f 0) ha hU n ≫
        (GammaSectionsComparison.nativeFlasqueCohomologyIsoOfZero K hK he n e).hom =
      Abelian.CechComparison.abelianCechToSheaf U F hU n := by
  let H := CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)
  have hcoef := abelianCechFlasqueComparison_coefficients U hK e.hom
    ((HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K).f 0) (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.zeroAugmentationSequence K).zero ha hU n
  rw [← hcoef, GammaSectionsComparison.nativeFlasqueCohomologyIsoOfZero, Iso.trans_hom,
    Category.assoc, ← Category.assoc
      (FlasqueCechD.abelianCechFlasqueComparison U hK ((HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K).f 0)
        (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.zeroAugmentationSequence K).zero hU n),
    GammaSectionsComparison.nativeFlasqueCohomologyIso_cech, ← Category.assoc,
    Abelian.CechComparison.abelianCechToSheaf_naturality]
  change (Abelian.CechComparison.abelianCechToSheaf U F hU n ≫ (H.mapIso e).hom) ≫ (H.mapIso e).inv = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.FlasqueCechCoefficients
