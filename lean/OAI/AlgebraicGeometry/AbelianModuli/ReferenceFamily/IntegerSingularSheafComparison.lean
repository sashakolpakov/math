import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientSingularSheafResolution
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InjectiveSingularSheafSections
import OAI.AlgebraicGeometry.SheafCohomology.IntegerCoefficients
import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.AugmentationNaturality

/-! # Integer Singular Sheaf Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntegerSingularSheafComparison

noncomputable section

/-! Actual singular cohomology compared with ordinary locally constant
abelian-sheaf cohomology for injective integral coefficient modules. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

open OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.AugmentationNaturality OAI.AlgebraicGeometry.SheafCohomology.IntegerCoefficients.Projective

abbrev integerModuleForget := forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}

variable (M : ModuleCat.{0} ℤ) (X : TopCat.{0})

def integerCoefficientSheafForget : TopCat.Sheaf (ModuleCat.{0} ℤ) X ⥤
    TopCat.Sheaf AddCommGrpCat.{0} X := SheafCohomology.IntegerCoefficients.Projective.integerSheafForget X

instance integerCoefficientSheafForget_equivalence : (integerCoefficientSheafForget X).IsEquivalence :=
  inferInstanceAs (SheafCohomology.IntegerCoefficients.Projective.integerSheafForget X).IsEquivalence

instance integerCoefficientSheafForget_additive : (integerCoefficientSheafForget X).Additive :=
  SheafCohomology.IntegerCoefficients.Projective.integerSheafForget_additive X

abbrev integerLocallyConstantAbelianSheaf : TopCat.Sheaf AddCommGrpCat.{0} X :=
  (integerCoefficientSheafForget X).obj (LocallyConstantModuleSheaf.coefficientLocallyConstantSheaf M X)

abbrev integerAbelianSingularResolution : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ :=
  ((integerCoefficientSheafForget X).mapHomologicalComplex (.up ℕ)).obj (CoefficientSingularSheafResolution.coefficientSingularSheafComplex M X)

def integerConstantAbelianZeroIso [LocallyPathConnectedSpace X] :
    integerLocallyConstantAbelianSheaf M X ≅ (integerAbelianSingularResolution M X).homology 0 :=
  (integerCoefficientSheafForget X).mapIso (CoefficientSingularSheafResolution.coefficientLocallyConstantSheafZeroIso M X) ≪≫
    (((CoefficientSingularSheafResolution.coefficientSingularSheafComplex M X).sc 0).mapHomologyIso (integerCoefficientSheafForget X)).symm

theorem integerAbelianSingularResolution_exact [StronglyLocallyContractibleSpace X] (n : ℕ) :
    (integerAbelianSingularResolution M X).ExactAt (n + 1) :=
  (CoefficientSingularSheafResolution.coefficientSingularSheaf_exact M X n).map (integerCoefficientSheafForget X)

theorem integerAbelianSingularResolution_flasque [MetrizableSpace X] (n : ℕ) :
    TopCat.Sheaf.IsFlasque ((integerAbelianSingularResolution M X).X n) := by
  have := CoefficientSingularSheafResolution.coefficientSingularSheaf_flasque M X n
  constructor
  intro U V i
  change Epi (integerModuleForget.map (((CoefficientSingularSheafResolution.coefficientSingularSheafComplex M X).X n).obj.map i))
  infer_instance

def integerSingularSectionsForgetIso :
    ((integerModuleForget.mapHomologicalComplex (.up ℕ)).obj (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularSheafGlobalSections M X)) ≅
      CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex (integerAbelianSingularResolution M X) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j _
    change integerModuleForget.map
      (((CoefficientSingularSheafResolution.coefficientSingularSheafComplex M X).d i j).hom.app (op ⊤)) ≫ 𝟙 _ =
        𝟙 _ ≫ integerModuleForget.map
          (((CoefficientSingularSheafResolution.coefficientSingularSheafComplex M X).d i j).hom.app (op ⊤))
    simp only [Category.comp_id, Category.id_comp])

def integerSingularSectionsHomologyIso (n : ℕ) :
    integerModuleForget.obj ((AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularSheafGlobalSections M X).homology n) ≅
      (CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex (integerAbelianSingularResolution M X)).homology n :=
  (((AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularSheafGlobalSections M X).sc n).mapHomologyIso integerModuleForget).symm ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (.up ℕ) n).mapIso
      (integerSingularSectionsForgetIso M X)

variable [StronglyLocallyContractibleSpace X] [LocallyPathConnectedSpace X]

def integerSingularBettiSheafMap (n : ℕ) :
    integerModuleForget.obj (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology M X (n + 1)) ⟶
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).obj
        (integerLocallyConstantAbelianSheaf M X) :=
  integerModuleForget.map (HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections M X) (n + 1)) ≫
    (integerSingularSectionsHomologyIso M X (n + 1)).hom ≫
    DivisorClass.Chern.Intrinsic.AugmentationNaturality.nativeSectionCohomologyMapOfZero (X := X) (integerAbelianSingularResolution M X)
      (integerAbelianSingularResolution_exact M X) (integerConstantAbelianZeroIso M X) n

theorem integerSingularBettiSheafMap_isIso [Injective M] [MetrizableSpace X] (n : ℕ) :
    IsIso (integerSingularBettiSheafMap M X n) := by
  let : MetricSpace X := metrizableSpaceMetric X
  have := InjectiveSingularSheafSections.InjectiveSingularComparison.quasiIso_singularCochainsToSheafSections M X
  have hi : IsIso (DivisorClass.Chern.Intrinsic.AugmentationNaturality.nativeSectionCohomologyMapOfZero (X := X) (integerAbelianSingularResolution M X)
      (integerAbelianSingularResolution_exact M X) (integerConstantAbelianZeroIso M X) n) := by
    have hc := DivisorClass.Chern.Intrinsic.SectionNaturality.nativeSectionCohomologyMap_eq_flasque (X := X) (integerAbelianSingularResolution M X)
      (integerAbelianSingularResolution_flasque M X) (integerAbelianSingularResolution_exact M X) n
    have : IsIso (DivisorClass.Chern.Intrinsic.SectionCohomologyMap.nativeSectionCohomologyMap (X := X) (integerAbelianSingularResolution M X)
        (integerAbelianSingularResolution_exact M X) n) :=
      (congrArg IsIso hc).mpr inferInstance
    unfold DivisorClass.Chern.Intrinsic.AugmentationNaturality.nativeSectionCohomologyMapOfZero
    exact IsIso.comp_isIso' this
      (((Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).mapIso
        (integerConstantAbelianZeroIso M X)).isIso_inv)
  unfold integerSingularBettiSheafMap
  infer_instance

def integerSingularBettiSheafIso [Injective M] [MetrizableSpace X] (n : ℕ) :
    integerModuleForget.obj (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology M X (n + 1)) ≅
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).obj
        (integerLocallyConstantAbelianSheaf M X) := by
  have := integerSingularBettiSheafMap_isIso M X n
  exact asIso (integerSingularBettiSheafMap M X n)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntegerSingularSheafComparison
