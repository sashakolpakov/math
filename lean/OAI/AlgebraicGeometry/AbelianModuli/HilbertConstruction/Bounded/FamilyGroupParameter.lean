import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.IntrinsicFamilyOperations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.Universal

/-! # Family Group Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FamilyGroupParameter

noncomputable section

/-! A concrete quasi-projective closed group-law parameter is obtained from the product of the bounded multiplication and inversion parameters and the unit-point family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

local instance boundedGroupProductProper {S : Scheme.{u}} (X Y : Over S) [IsProper X.hom] [IsProper Y.hom] :
    IsProper (X ⊗ Y).hom := inferInstanceAs (IsProper (pullback.fst X.hom Y.hom ≫ X.hom))

local instance boundedGroupProductSmooth {S : Scheme.{u}} (X Y : Over S) [Smooth X.hom] [Smooth Y.hom] :
    Smooth (X ⊗ Y).hom := inferInstanceAs (Smooth (pullback.fst X.hom Y.hom ≫ X.hom))

local instance boundedGroupPullbackProper {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [IsProper A.hom] :
    IsProper ((Over.pullback f).obj A).hom := inferInstanceAs (IsProper (pullback.snd A.hom f))

local instance boundedGroupPullbackSmooth {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [Smooth A.hom] :
    Smooth ((Over.pullback f).obj A).hom := inferInstanceAs (Smooth (pullback.snd A.hom f))

variable {S : Scheme.{u}} [IsNoetherian S] {A : Over S} [IsProper A.hom] [Smooth A.hom]
variable {nm ni : ℕ} (jm : (A ⊗ A) ⊗ A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S nm)
variable (ji : A ⊗ A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S ni)
variable [IsClosedImmersion jm.left] [IsClosedImmersion ji.left] (Pm Pi : Polynomial ℚ)
variable (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation A)

def boundedFamilyGroupParameter : Over S := by
  have : IsNoetherian (FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi).left :=
    (FamilyOperationParameters.boundedFamilyOperationParameterQuasiProjectivePresentation jm ji Pm Pi Q).noetherian
  exact Family.CommutativeGroupParameter.familyCommutativeGroupParameter (FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi)
    (IntrinsicFamilyOperations.boundedFamilyUniversalOperations jm ji Pm Pi)

def boundedFamilyGroupParameterInclusion :
    boundedFamilyGroupParameter jm ji Pm Pi Q ⟶ FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi := by
  have : IsNoetherian (FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi).left :=
    (FamilyOperationParameters.boundedFamilyOperationParameterQuasiProjectivePresentation jm ji Pm Pi Q).noetherian
  exact Family.CommutativeGroupParameter.familyCommutativeGroupParameterInclusion (FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi)
    (IntrinsicFamilyOperations.boundedFamilyUniversalOperations jm ji Pm Pi)

instance boundedFamilyGroupParameterInclusion_closed :
    IsClosedImmersion (boundedFamilyGroupParameterInclusion jm ji Pm Pi Q).left := by
  have : IsNoetherian (FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi).left :=
    (FamilyOperationParameters.boundedFamilyOperationParameterQuasiProjectivePresentation jm ji Pm Pi Q).noetherian
  exact Family.CommutativeGroupParameter.familyCommutativeGroupParameterInclusion_closed (FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi)
    (IntrinsicFamilyOperations.boundedFamilyUniversalOperations jm ji Pm Pi)

def boundedFamilyGroupParameterQuasiProjectivePresentation :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (boundedFamilyGroupParameter jm ji Pm Pi Q) :=
  (FamilyOperationParameters.boundedFamilyOperationParameterQuasiProjectivePresentation jm ji Pm Pi Q).ofClosedImmersion
    (boundedFamilyGroupParameterInclusion jm ji Pm Pi Q)

def boundedFamilyGroupParameterPointEquiv (T : Over S) :
    (T ⟶ boundedFamilyGroupParameter jm ji Pm Pi Q) ≃
      {c : T ⟶ FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi //
        ((IntrinsicFamilyOperations.boundedFamilyUniversalOperations jm ji Pm Pi).baseChange c.left).Laws} := by
  have : IsNoetherian (FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi).left :=
    (FamilyOperationParameters.boundedFamilyOperationParameterQuasiProjectivePresentation jm ji Pm Pi Q).noetherian
  exact Family.CommutativeGroupParameter.familyCommutativeGroupParameterPointEquiv (FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi)
    (IntrinsicFamilyOperations.boundedFamilyUniversalOperations jm ji Pm Pi) T

def boundedFamilyGroupUniversalFamily : Over (boundedFamilyGroupParameter jm ji Pm Pi Q).left :=
  (Over.pullback (boundedFamilyGroupParameterInclusion jm ji Pm Pi Q).left).obj
    ((Over.pullback (FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi).hom).obj A)

@[instance_reducible] def boundedFamilyGroupUniversalGroupObj :
    GrpObj (boundedFamilyGroupUniversalFamily jm ji Pm Pi Q) := by
  have : IsNoetherian (FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi).left :=
    (FamilyOperationParameters.boundedFamilyOperationParameterQuasiProjectivePresentation jm ji Pm Pi Q).noetherian
  exact Family.CommutativeGroupParameter.familyCommutativeGroupUniversalGroupObj (FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi)
    (IntrinsicFamilyOperations.boundedFamilyUniversalOperations jm ji Pm Pi)

theorem boundedFamilyGroupUniversalGroupObj_comm :
    letI := boundedFamilyGroupUniversalGroupObj jm ji Pm Pi Q
    IsCommMonObj (boundedFamilyGroupUniversalFamily jm ji Pm Pi Q) := by
  have : IsNoetherian (FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi).left :=
    (FamilyOperationParameters.boundedFamilyOperationParameterQuasiProjectivePresentation jm ji Pm Pi Q).noetherian
  exact Family.CommutativeGroupParameter.familyCommutativeGroupUniversalGroupObj_comm (FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi)
    (IntrinsicFamilyOperations.boundedFamilyUniversalOperations jm ji Pm Pi)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FamilyGroupParameter
