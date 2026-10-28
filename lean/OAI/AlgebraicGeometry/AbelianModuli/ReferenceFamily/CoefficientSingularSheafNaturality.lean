import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientSingularSheafResolution
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularPeriodCoefficients
import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.AugmentationNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientComparisonDiagrams

/-! # Coefficient Singular Sheaf Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientSingularSheafNaturality

noncomputable section

/-! Coefficient maps preserve the actual singular presheaf augmentation
and its resulting degree-zero sheaf identification. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

open OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.AugmentationNaturality

variable {R : Type} [Ring R] {M N : ModuleCat.{0} R} (f : M ⟶ N) (X : TopCat.{0})

def coefficientSingularPresheafMap : AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X ⟶ AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex N X where
  f n := {
    app U := (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap f (TopCat.of U.unop)).f n
    naturality _ _ i := congrArg (fun g => g.f n)
      (AlgebraicTopology.Cohomology.Singular.Functor.coefficientCochainMap_naturality f ((Opens.toTopCat X).map i.unop)) }
  comm' i j _ := by
    apply NatTrans.ext
    funext U
    exact (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap f (TopCat.of U.unop)).comm i j

def coefficientSingularSheafMap : CoefficientSingularSheafResolution.coefficientSingularSheafComplex M X ⟶ CoefficientSingularSheafResolution.coefficientSingularSheafComplex N X :=
  ((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R)).mapHomologicalComplex (.up ℕ)).map
    (coefficientSingularPresheafMap f X)

theorem coefficientSingularPresheafMap_augmentation :
    LocallyConstantModuleSheaf.coefficientLocallyConstantAugmentation M X ≫ (coefficientSingularPresheafMap f X).f 0 =
      (LocallyConstantModuleSheaf.coefficientLocallyConstantSheafMap M X f).hom ≫ LocallyConstantModuleSheaf.coefficientLocallyConstantAugmentation N X := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso N (TopCat.of U.unop)).toLinearEquiv.injective
  change (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso N (TopCat.of U.unop)).hom
    ((AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap f (TopCat.of U.unop)).f 0 (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero M (TopCat.of U.unop) a)) =
      (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso N (TopCat.of U.unop)).hom
        (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero N (TopCat.of U.unop)
          ((LocallyConstantModuleSheaf.coefficientLocallyConstantSheafMap M X f).hom.app U a))
  ext x
  rw [SingularPeriodCoefficients.IntegralSingularPeriods.coefficient_zero_point,
    AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero_apply M (TopCat.of U.unop) a x]
  exact (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero_apply N (TopCat.of U.unop)
    ((LocallyConstantModuleSheaf.coefficientLocallyConstantSheafMap M X f).hom.app U a) x).symm

variable [LocallyPathConnectedSpace X]

theorem coefficientLocallyConstantPresheafZeroIso_augmentation (A : ModuleCat.{0} R) :
    (CoefficientSingularSheafResolution.coefficientLocallyConstantPresheafZeroIso A X).hom ≫
      (HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex A X)).f 0 =
        LocallyConstantModuleSheaf.coefficientLocallyConstantAugmentation A X := by
  rw [HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation_f_zero, CoefficientSingularSheafResolution.coefficientLocallyConstantPresheafZeroIso,
    Iso.trans_hom, Category.assoc, Iso.hom_inv_id_assoc]
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

theorem coefficientLocallyConstantPresheafZeroIso_naturality :
    (CoefficientSingularSheafResolution.coefficientLocallyConstantPresheafZeroIso M X).hom ≫
      HomologicalComplex.homologyMap (coefficientSingularPresheafMap f X) 0 =
    (LocallyConstantModuleSheaf.coefficientLocallyConstantSheafMap M X f).hom ≫
      (CoefficientSingularSheafResolution.coefficientLocallyConstantPresheafZeroIso N X).hom :=
  DivisorClass.Chern.Intrinsic.AugmentationNaturality.cochainAugmentationZeroIso_naturality _ _ _ _ _ _
    (coefficientLocallyConstantPresheafZeroIso_augmentation X M)
    (coefficientLocallyConstantPresheafZeroIso_augmentation X N)
    (coefficientSingularPresheafMap_augmentation f X)

theorem coefficientLocallyConstantSheafZeroIso_naturality :
    (CoefficientSingularSheafResolution.coefficientLocallyConstantSheafZeroIso M X).hom ≫
      HomologicalComplex.homologyMap (coefficientSingularSheafMap f X) 0 =
    LocallyConstantModuleSheaf.coefficientLocallyConstantSheafMap M X f ≫
      (CoefficientSingularSheafResolution.coefficientLocallyConstantSheafZeroIso N X).hom := by
  let S := presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R)
  have hn := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ 0).map (coefficientSingularPresheafMap f X)) S
  have hs : (sheafificationIso (LocallyConstantModuleSheaf.coefficientLocallyConstantSheaf M X)).hom ≫
      S.map (LocallyConstantModuleSheaf.coefficientLocallyConstantSheafMap M X f).hom =
        LocallyConstantModuleSheaf.coefficientLocallyConstantSheafMap M X f ≫
          (sheafificationIso (LocallyConstantModuleSheaf.coefficientLocallyConstantSheaf N X)).hom := by
    apply Sheaf.hom_ext
    exact (CategoryTheory.toSheafify_naturality (Opens.grothendieckTopology X)
      (LocallyConstantModuleSheaf.coefficientLocallyConstantSheafMap M X f).hom).symm
  have hp := congrArg S.map (coefficientLocallyConstantPresheafZeroIso_naturality f X)
  have hp' : S.map (CoefficientSingularSheafResolution.coefficientLocallyConstantPresheafZeroIso M X).hom ≫
      S.map (HomologicalComplex.homologyMap (coefficientSingularPresheafMap f X) 0) =
    S.map (LocallyConstantModuleSheaf.coefficientLocallyConstantSheafMap M X f).hom ≫
      S.map (CoefficientSingularSheafResolution.coefficientLocallyConstantPresheafZeroIso N X).hom :=
    (S.map_comp _ _).symm.trans (hp.trans (S.map_comp _ _))
  exact CoefficientComparisonDiagrams.three_comparison_squares _ _ _ _ _ _ _ _ _ _ hs hp' hn.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientSingularSheafNaturality
