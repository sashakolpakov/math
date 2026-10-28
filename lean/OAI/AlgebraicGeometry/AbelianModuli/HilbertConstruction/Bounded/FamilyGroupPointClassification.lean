import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FamilyGroupParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.OperationParameterNaturality

/-! # Family Group Point Classification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FamilyGroupPointClassification

noncomputable section

/-! Points of the concrete bounded group-law parameter are exactly actual commutative-group operations with the prescribed graph polynomials, on every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

local instance boundedGroupPointProductProper {S : Scheme.{u}} (X Y : Over S) [IsProper X.hom] [IsProper Y.hom] :
    IsProper (X ⊗ Y).hom := inferInstanceAs (IsProper (pullback.fst X.hom Y.hom ≫ X.hom))

local instance boundedGroupPointProductSmooth {S : Scheme.{u}} (X Y : Over S) [Smooth X.hom] [Smooth Y.hom] :
    Smooth (X ⊗ Y).hom := inferInstanceAs (Smooth (pullback.fst X.hom Y.hom ≫ X.hom))

variable {S : Scheme.{u}} [IsNoetherian S] {A : Over S} [IsProper A.hom] [Smooth A.hom]
variable {nm ni : ℕ} (jm : (A ⊗ A) ⊗ A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S nm)
variable (ji : A ⊗ A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S ni)
variable [IsClosedImmersion jm.left] [IsClosedImmersion ji.left] (Pm Pi : Polynomial ℚ)

theorem boundedFamilyUniversalOperations_point {T : Over S}
    (c : T ⟶ FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi) :
    (IntrinsicFamilyOperations.boundedFamilyOperationParameterNativeEquiv jm ji Pm Pi T c).val =
      (IntrinsicFamilyOperations.boundedFamilyUniversalOperations jm ji Pm Pi).geometricBaseChange c := by
  have h := OperationParameterNaturality.boundedFamilyOperationParameterNativeEquiv_natural jm ji Pm Pi c (𝟙 _)
  rw [Category.comp_id] at h
  exact h

theorem boundedFamilyGroupCondition_iff {T : Over S}
    (c : T ⟶ FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi) :
    (IntrinsicFamilyOperations.boundedFamilyOperationParameterNativeEquiv jm ji Pm Pi T c).val.Laws ↔
      ((IntrinsicFamilyOperations.boundedFamilyUniversalOperations jm ji Pm Pi).baseChange c.left).Laws := by
  rw [boundedFamilyUniversalOperations_point]
  exact (IntrinsicFamilyOperations.boundedFamilyUniversalOperations jm ji Pm Pi).geometricBaseChange_laws_iff c

def BoundedCommutativeFamilyGroupOperations (T : Over S) :=
  {D : IntrinsicFamilyOperations.BoundedFamilyGroupOperations jm ji Pm Pi T // D.val.Laws}

def boundedFamilyGroupParameterNativeEquiv (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation A) (T : Over S) :
    (T ⟶ FamilyGroupParameter.boundedFamilyGroupParameter jm ji Pm Pi Q) ≃ BoundedCommutativeFamilyGroupOperations jm ji Pm Pi T :=
  (FamilyGroupParameter.boundedFamilyGroupParameterPointEquiv jm ji Pm Pi Q T).trans
    ((IntrinsicFamilyOperations.boundedFamilyOperationParameterNativeEquiv jm ji Pm Pi T).subtypeEquiv
      (fun c => (boundedFamilyGroupCondition_iff jm ji Pm Pi c).symm))

theorem boundedFamilyGroup_quasiProjective_point_classification (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation A) :
    ∃ Z : Over S, Nonempty (Projective.ProjectivePresentations.QuasiProjectivePresentation Z) ∧
      ∀ T : Over S, Nonempty ((T ⟶ Z) ≃ BoundedCommutativeFamilyGroupOperations jm ji Pm Pi T) :=
  ⟨FamilyGroupParameter.boundedFamilyGroupParameter jm ji Pm Pi Q,
    ⟨FamilyGroupParameter.boundedFamilyGroupParameterQuasiProjectivePresentation jm ji Pm Pi Q⟩,
    fun T => ⟨boundedFamilyGroupParameterNativeEquiv jm ji Pm Pi Q T⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FamilyGroupPointClassification
