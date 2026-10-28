import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.EquivalenceCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.SectionCokernelCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionMultiplication
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConcreteModuleTensorAssociativity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.UnitRight

/-! # Twist Iteration -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TwistIteration

noncomputable section

/-! Iteration of the actual line-bundle tensor equivalence is identified with the constructed tensor-power sheaves. Regular-section multiplication gives a monomorphism into that equivalence. -/
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry
universe u
local instance twistIterationMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Module.SheafMonoidal.moduleMonoidalCategory X
local instance twistIterationSymmetric (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Module.SheafMonoidal.moduleSymmetricCategory X
variable {X : Scheme.{u}}

def actualModuleTensorComm (M N : X.Modules) : Tensor.ProductSheaf.tensorModule M N ≅ Tensor.ProductSheaf.tensorModule N M :=
  (Module.MonoidalTensorComparison.moduleMonoidalTensorIso M N).symm ≪≫ β_ M N ≪≫ Module.MonoidalTensorComparison.moduleMonoidalTensorIso N M

def lineBundleTwistIterationIso (L : Line.Bundles.LineBundle X) (n : ℕ) (M : X.Modules) :
    (Iterated.EquivalenceCohomology.iterateAutoEquivalence (TensorEquivalence.lineBundleRightTensorEquivalence L) n).functor.obj M ≅
      Tensor.ProductSheaf.tensorModule M (L.tensorPower n).sheaf := by
  induction n generalizing M with
  | zero =>
    exact (Tensor.UnitRight.tensorModuleUnitRightIso M).symm ≪≫
      Tensor.Bifunctor.tensorModuleMapIso (Iso.refl M) L.tensorPowerZeroIso.symm
  | succ n ih =>
    change (Iterated.EquivalenceCohomology.iterateAutoEquivalence (TensorEquivalence.lineBundleRightTensorEquivalence L) n).functor.obj
      ((TensorEquivalence.lineBundleRightTensorEquivalence L).functor.obj M) ≅ _
    exact ih ((TensorEquivalence.lineBundleRightTensorEquivalence L).functor.obj M) ≪≫
      Tensor.Bifunctor.tensorModuleMapIso (TensorEquivalence.lineBundleRightTensorEquivalence_objIso L M)
        (Iso.refl (L.tensorPower n).sheaf) ≪≫
      ConcreteModuleTensorAssociativity.actualModuleTensorAssoc M L.sheaf (L.tensorPower n).sheaf ≪≫
      Tensor.Bifunctor.tensorModuleMapIso (Iso.refl M) (L.tensor_succ_sheafIso n).some

def regularSectionToRightTensor (L : Line.Bundles.LineBundle X) (M : X.Modules)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) : M ⟶ (TensorEquivalence.lineBundleRightTensorEquivalence L).functor.obj M :=
  Module.SectionMultiplication.moduleSectionMultiply L M s ≫ (actualModuleTensorComm L.sheaf M).hom ≫
    (TensorEquivalence.lineBundleRightTensorEquivalence_objIso L M).inv

theorem regularSectionToRightTensor_mono (L : Line.Bundles.LineBundle X) (M : X.Modules)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) [Mono (Module.SectionMultiplication.moduleSectionMultiply L M s)] :
    Mono (regularSectionToRightTensor L M s) := by
  dsimp only [regularSectionToRightTensor]
  infer_instance

theorem lineBundleTwistIteration_euler
    {K : Type u} [Field K] (p : X ⟶ Spec (.of K))
    (L : Line.Bundles.LineBundle X) (M : X.Modules) (n : ℕ) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic p
        ((Iterated.EquivalenceCohomology.iterateAutoEquivalence (TensorEquivalence.lineBundleRightTensorEquivalence L) n).functor.obj M) =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (Tensor.ProductSheaf.tensorModule M (L.tensorPower n).sheaf) :=
  Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso p (lineBundleTwistIterationIso L n M)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TwistIteration
