import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LocallyConstantModuleSheaf
import OAI.AlgebraicTopology.Cohomology.Singular.StalkExactness
import OAI.AlgebraicTopology.Cohomology.Singular.SheafFlasque

/-! # Coefficient Singular Sheaf Resolution -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientSingularSheafResolution

noncomputable section

/-! The singular sheaf complex resolves the actual locally constant sheaf
for every coefficient module. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

attribute [local instance] AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkModulesForget₂PreservesFilteredColimits
  AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkModulesForgetPreservesFilteredColimits

variable {R : Type} [Ring R] (M : ModuleCat.{0} R) (X : TopCat.{0})

abbrev coefficientSingularSheafComplex := AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X)

theorem coefficientLocallyConstantAugmentation_d :
    LocallyConstantModuleSheaf.coefficientLocallyConstantAugmentation M X ≫ (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X).d 0 1 = 0 := by
  apply NatTrans.ext
  funext U
  exact AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero_d M (TopCat.of U.unop)

def coefficientLocallyConstantAugmentation_kernel [LocallyPathConnectedSpace X] :
    IsLimit (KernelFork.ofι (LocallyConstantModuleSheaf.coefficientLocallyConstantAugmentation M X)
      (coefficientLocallyConstantAugmentation_d M X)) := by
  apply evaluationJointlyReflectsLimits
  intro U
  refine (isLimitMapConeForkEquiv'
    ((evaluation (Opens X)ᵒᵖ (ModuleCat.{0} R)).obj U)
    (coefficientLocallyConstantAugmentation_d M X)).symm ?_
  have : LocallyPathConnectedSpace U.unop := U.unop.isOpen.locallyPathConnectedSpace
  exact AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero_isKernel M (TopCat.of U.unop)

def coefficientLocallyConstantPresheafZeroIso [LocallyPathConnectedSpace X] :
    LocallyConstantModuleSheaf.coefficientLocallyConstantPresheaf M X ≅ (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X).homology 0 :=
  (coefficientLocallyConstantAugmentation_kernel M X).conePointUniqueUpToIso
    ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X).cyclesIsKernel 0 1
      ((ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 0 1 from rfl))) ≪≫
        (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X).isoHomologyπ₀

def coefficientLocallyConstantSheafZeroIso [LocallyPathConnectedSpace X] :
    LocallyConstantModuleSheaf.coefficientLocallyConstantSheaf M X ≅ (coefficientSingularSheafComplex M X).homology 0 :=
  sheafificationIso (LocallyConstantModuleSheaf.coefficientLocallyConstantSheaf M X) ≪≫
    (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R)).mapIso
      (coefficientLocallyConstantPresheafZeroIso M X) ≪≫
    (((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X).sc 0).mapHomologyIso
      (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R))).symm

theorem coefficientSingularSheaf_exact [StronglyLocallyContractibleSpace X] (n : ℕ) :
    (coefficientSingularSheafComplex M X).ExactAt (n + 1) := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
    ((coefficientSingularSheafComplex M X).sc (n + 1))).mpr
  intro x
  exact (AlgebraicTopology.Cohomology.Singular.StalkExactness.singularStalkComplex_exactAt_succ M X x n).of_iso
    (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafificationStalkComplexIso (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X) x)

theorem coefficientSingularSheaf_flasque [MetrizableSpace X] (n : ℕ) :
    TopCat.Sheaf.IsFlasque ((coefficientSingularSheafComplex M X).X n) :=
  AlgebraicTopology.Cohomology.Singular.SheafFlasque.sheafifiedSingularCochains_isFlasque_of_metrizable M X n

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientSingularSheafResolution
