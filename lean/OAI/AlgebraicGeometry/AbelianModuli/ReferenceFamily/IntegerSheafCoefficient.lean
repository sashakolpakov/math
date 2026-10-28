import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularSheafSectionCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LocallyConstantCoefficientExact

/-! # Integer Sheaf Coefficient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntegerSheafCoefficient

noncomputable section

section

/-! Actual coefficient maps through the integer-to-abelian sheaf and
global-section comparisons. -/

open _root_.CategoryTheory _root_.TopologicalSpace

variable {M N : ModuleCat.{0} ℤ} (f : M ⟶ N) (X : TopCat.{0})

def integerAbelianSingularMap : IntegerSingularSheafComparison.integerAbelianSingularResolution M X ⟶ IntegerSingularSheafComparison.integerAbelianSingularResolution N X :=
  ((IntegerSingularSheafComparison.integerCoefficientSheafForget X).mapHomologicalComplex (.up ℕ)).map (CoefficientSingularSheafNaturality.coefficientSingularSheafMap f X)

theorem integerConstantAbelianZeroIso_naturality [LocallyPathConnectedSpace X] :
    (IntegerSingularSheafComparison.integerConstantAbelianZeroIso M X).hom ≫
      HomologicalComplex.homologyMap (integerAbelianSingularMap f X) 0 =
    LocallyConstantCoefficientExact.integerLocallyConstantSheafMap f X ≫ (IntegerSingularSheafComparison.integerConstantAbelianZeroIso N X).hom := by
  let F := IntegerSingularSheafComparison.integerCoefficientSheafForget X
  have hp := congrArg F.map (CoefficientSingularSheafNaturality.coefficientLocallyConstantSheafZeroIso_naturality f X)
  have hp' : F.map (CoefficientSingularSheafResolution.coefficientLocallyConstantSheafZeroIso M X).hom ≫
      F.map (HomologicalComplex.homologyMap (CoefficientSingularSheafNaturality.coefficientSingularSheafMap f X) 0) =
    F.map (LocallyConstantModuleSheaf.coefficientLocallyConstantSheafMap M X f) ≫
      F.map (CoefficientSingularSheafResolution.coefficientLocallyConstantSheafZeroIso N X).hom :=
    (F.map_comp _ _).symm.trans (hp.trans (F.map_comp _ _))
  have hn := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ 0).map (CoefficientSingularSheafNaturality.coefficientSingularSheafMap f X)) F
  exact CoefficientComparisonDiagrams.two_comparison_squares _ _ _ _ _ _ _ hp' hn.symm

def integerAbelianSectionsMap :
    CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex (IntegerSingularSheafComparison.integerAbelianSingularResolution M X) ⟶
      CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex (IntegerSingularSheafComparison.integerAbelianSingularResolution N X) :=
  ((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSections X).mapHomologicalComplex (.up ℕ)).map (integerAbelianSingularMap f X)

theorem integerSingularSectionsForgetIso_naturality :
    ((IntegerSingularSheafComparison.integerModuleForget.mapHomologicalComplex (.up ℕ)).map (SingularSheafSectionCoefficients.coefficientSheafSectionsMap f X)) ≫
      (IntegerSingularSheafComparison.integerSingularSectionsForgetIso N X).hom =
    (IntegerSingularSheafComparison.integerSingularSectionsForgetIso M X).hom ≫ integerAbelianSectionsMap f X := by
  apply HomologicalComplex.Hom.ext
  funext n
  change IntegerSingularSheafComparison.integerModuleForget.map ((SingularSheafSectionCoefficients.coefficientSheafSectionsMap f X).f n) ≫ 𝟙 _ =
    𝟙 _ ≫ IntegerSingularSheafComparison.integerModuleForget.map ((SingularSheafSectionCoefficients.coefficientSheafSectionsMap f X).f n)
  exact (Category.comp_id _).trans (Category.id_comp _).symm

theorem integerSingularSectionsHomologyIso_naturality (n : ℕ) :
    IntegerSingularSheafComparison.integerModuleForget.map (HomologicalComplex.homologyMap (SingularSheafSectionCoefficients.coefficientSheafSectionsMap f X) n) ≫
      (IntegerSingularSheafComparison.integerSingularSectionsHomologyIso N X n).hom =
    (IntegerSingularSheafComparison.integerSingularSectionsHomologyIso M X n).hom ≫
      HomologicalComplex.homologyMap (integerAbelianSectionsMap f X) n := by
  have hn := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map (SingularSheafSectionCoefficients.coefficientSheafSectionsMap f X)) IntegerSingularSheafComparison.integerModuleForget
  have hp := congrArg (fun u => HomologicalComplex.homologyMap u n)
    (integerSingularSectionsForgetIso_naturality f X)
  have hp' : HomologicalComplex.homologyMap (IntegerSingularSheafComparison.integerSingularSectionsForgetIso M X).hom n ≫
      HomologicalComplex.homologyMap (integerAbelianSectionsMap f X) n =
    HomologicalComplex.homologyMap
        ((IntegerSingularSheafComparison.integerModuleForget.mapHomologicalComplex (.up ℕ)).map (SingularSheafSectionCoefficients.coefficientSheafSectionsMap f X)) n ≫
      HomologicalComplex.homologyMap (IntegerSingularSheafComparison.integerSingularSectionsForgetIso N X).hom n :=
    (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
      (hp.symm.trans (HomologicalComplex.homologyMap_comp _ _ n))
  exact (CoefficientComparisonDiagrams.two_comparison_squares _ _ _ _ _ _ _ hn.symm hp').symm

end

section

/-! The actual singular-to-sheaf comparison commutes with every integral
coefficient morphism. -/

open _root_.CategoryTheory _root_.TopologicalSpace

variable {M N : ModuleCat.{0} ℤ} (f : M ⟶ N) (X : TopCat.{0})
  [StronglyLocallyContractibleSpace X] [LocallyPathConnectedSpace X]

theorem integerSingularBettiSheafMap_naturality (n : ℕ) :
    IntegerSingularSheafComparison.integerModuleForget.map (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap f X (n + 1)) ≫ IntegerSingularSheafComparison.integerSingularBettiSheafMap N X n =
      IntegerSingularSheafComparison.integerSingularBettiSheafMap M X n ≫
        (Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).map
          (LocallyConstantCoefficientExact.integerLocallyConstantSheafMap f X) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (.up ℕ) (n + 1) ⋙ IntegerSingularSheafComparison.integerModuleForget
  have hp := congrArg H.map (SingularSheafSectionCoefficients.singularCochainsToSheafSections_coefficient f X).symm
  have hp' : H.map (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections M X) ≫ H.map (SingularSheafSectionCoefficients.coefficientSheafSectionsMap f X) =
      H.map (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap f X) ≫ H.map (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections N X) :=
    (H.map_comp _ _).symm.trans (hp.trans (H.map_comp _ _))
  have hn := DivisorClass.Chern.Intrinsic.AugmentationNaturality.nativeSectionCohomologyMapOfZero_naturality (X := X)
    (integerAbelianSingularMap f X) (IntegerSingularSheafComparison.integerAbelianSingularResolution_exact M X)
    (IntegerSingularSheafComparison.integerAbelianSingularResolution_exact N X) (LocallyConstantCoefficientExact.integerLocallyConstantSheafMap f X)
    (IntegerSingularSheafComparison.integerConstantAbelianZeroIso M X) (IntegerSingularSheafComparison.integerConstantAbelianZeroIso N X)
    (integerConstantAbelianZeroIso_naturality f X) n
  exact (CoefficientComparisonDiagrams.three_comparison_squares _ _ _ _ _ _ _ _ _ _ hp'
    (integerSingularSectionsHomologyIso_naturality f X (n + 1)).symm hn.symm).symm

end

/-! Transfer a proved singular H¹ coefficient lift into actual sheaf
cohomology through the native comparison and its proved naturality. -/

open _root_.CategoryTheory _root_.TopologicalSpace

variable {M N : ModuleCat.{0} ℤ} (f : M ⟶ N) (X : TopCat.{0})
  [StronglyLocallyContractibleSpace X] [LocallyPathConnectedSpace X] [MetrizableSpace X]
  [Injective N]

theorem sheafH1_coefficient_surjective_of_singular
    (h1 : Function.Surjective (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap f X 1)) :
    Function.Surjective ((Sheaf.functorH (Opens.grothendieckTopology X) 1).map
      (LocallyConstantCoefficientExact.integerLocallyConstantSheafMap f X)) := by
  intro a
  obtain ⟨b, hb⟩ := (IntegerSingularSheafComparison.integerSingularBettiSheafIso N X 0).addCommGroupIsoToAddEquiv.surjective a
  obtain ⟨c, hc⟩ := h1 b
  refine ⟨IntegerSingularSheafComparison.integerSingularBettiSheafMap M X 0 c, ?_⟩
  have hn := ConcreteCategory.congr_hom (integerSingularBettiSheafMap_naturality f X 0) c
  have hm : IntegerSingularSheafComparison.integerSingularBettiSheafMap N X 0 (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap f X 1 c) = a :=
    (congrArg (IntegerSingularSheafComparison.integerSingularBettiSheafMap N X 0) hc).trans hb
  exact hn.symm.trans hm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntegerSheafCoefficient
