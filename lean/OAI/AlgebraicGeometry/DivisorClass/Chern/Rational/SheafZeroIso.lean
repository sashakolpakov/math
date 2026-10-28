import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ConstantSheaf
import OAI.AlgebraicTopology.Cohomology.Singular.SheafQuasiIso

/-! # Sheaf Zero Iso -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SheafZeroIso

noncomputable section

/-!
# ChernClass: actual rational locally constant functions are singular degree-zero sheaf cohomology

The isomorphism uses the original point-evaluation augmentation, its
proved kernel property on every open set, and exact sheafification.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open OAI.AlgebraicTopology.Cohomology.Singular.SheafQuasiIso

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech

variable (X : TopCat.{0})

theorem locallyConstantRationalAugmentation_d :
    Cech.Obj.RationalCech.locallyConstantSingularAugmentation X ≫
      (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).d 0 1 = 0 := by
  apply NatTrans.ext
  funext U
  exact AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero_d (ModuleCat.of ℚ ℚ) (TopCat.of U.unop)

def locallyConstantRationalAugmentation_kernel [LocallyPathConnectedSpace X] :
    IsLimit (KernelFork.ofι (Cech.Obj.RationalCech.locallyConstantSingularAugmentation X)
      (locallyConstantRationalAugmentation_d X)) := by
  apply evaluationJointlyReflectsLimits
  intro U
  refine (isLimitMapConeForkEquiv'
    ((evaluation (Opens X)ᵒᵖ (ModuleCat.{0} ℚ)).obj U)
    (locallyConstantRationalAugmentation_d X)).symm ?_
  have : LocallyPathConnectedSpace U.unop := U.unop.isOpen.locallyPathConnectedSpace
  exact AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero_isKernel (ModuleCat.of ℚ ℚ) (TopCat.of U.unop)

def locallyConstantRationalPresheafZeroIso [LocallyPathConnectedSpace X] :
    Cech.Obj.RationalCech.locallyConstantPresheaf X ≅ (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).homology 0 :=
  (locallyConstantRationalAugmentation_kernel X).conePointUniqueUpToIso
    ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).cyclesIsKernel 0 1
      ((ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 0 1 from rfl))) ≪≫
      (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).isoHomologyπ₀

def locallyConstantRationalSheafZeroIso [LocallyPathConnectedSpace X] :
    ConstantSheaf.RationalCech.locallyConstantRationalSheaf X ≅
      (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)).homology 0 :=
  sheafificationIso (ConstantSheaf.RationalCech.locallyConstantRationalSheaf X) ≪≫
    (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).mapIso
      (locallyConstantRationalPresheafZeroIso X) ≪≫
    (((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).sc 0).mapHomologyIso
      (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ))).symm

end RationalCech

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SheafZeroIso
