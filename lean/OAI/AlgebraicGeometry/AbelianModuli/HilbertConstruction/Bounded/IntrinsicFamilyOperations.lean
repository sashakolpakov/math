import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FamilyOperationParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyOperationData

/-! # Intrinsic Family Operations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.IntrinsicFamilyOperations

noncomputable section

/-! The operation parameter classifies native multiplication, inversion, and unit operations with the prescribed embedded graph polynomials. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

def pairedOperationSubtypeEquiv {M I U : Type u} (p : M → Prop) (q : I → Prop) :
    (({m // p m} × {i // q i}) × U) ≃ {d : (M × I) × U // p d.1.1 ∧ q d.1.2} where
  toFun d := ⟨((d.1.1.val, d.1.2.val), d.2), d.1.1.property, d.1.2.property⟩
  invFun d := ((⟨d.val.1.1, d.property.1⟩, ⟨d.val.1.2, d.property.2⟩), d.val.2)
  left_inv _ := rfl
  right_inv _ := rfl

local instance boundedNativeProductProper {S : Scheme.{u}} (X Y : Over S) [IsProper X.hom] [IsProper Y.hom] :
    IsProper (X ⊗ Y).hom := inferInstanceAs (IsProper (pullback.fst X.hom Y.hom ≫ X.hom))

local instance boundedNativeProductSmooth {S : Scheme.{u}} (X Y : Over S) [Smooth X.hom] [Smooth Y.hom] :
    Smooth (X ⊗ Y).hom := inferInstanceAs (Smooth (pullback.fst X.hom Y.hom ≫ X.hom))

variable {S : Scheme.{u}} [IsNoetherian S] {A : Over S} [IsProper A.hom] [Smooth A.hom]
variable {nm ni : ℕ} (jm : (A ⊗ A) ⊗ A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S nm)
variable (ji : A ⊗ A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S ni)
variable [IsClosedImmersion jm.left] [IsClosedImmersion ji.left] (Pm Pi : Polynomial ℚ)

def BoundedFamilyGroupOperations (T : Over S) :=
  {D : FamilyGroup.Operations.FamilyGroupOperations ((Over.pullback T.hom).obj A) //
    ((Intrinsic.FamilyOperationData.familyOperationDataEquiv A T).symm D).1.1 ∈ (EmbeddedMorphismFunctor.boundedEmbeddedMorphismSubfunctor jm Pm).obj (Opposite.op T) ∧
    ((Intrinsic.FamilyOperationData.familyOperationDataEquiv A T).symm D).1.2 ∈ (EmbeddedMorphismFunctor.boundedEmbeddedMorphismSubfunctor ji Pi).obj (Opposite.op T)}

def boundedFamilyOperationDataEquiv (T : Over S) :
    (((EmbeddedMorphismFunctor.boundedEmbeddedMorphismFunctor jm Pm).obj (Opposite.op T) ×
      (EmbeddedMorphismFunctor.boundedEmbeddedMorphismFunctor ji Pi).obj (Opposite.op T)) × (T ⟶ A)) ≃
      BoundedFamilyGroupOperations jm ji Pm Pi T :=
  (pairedOperationSubtypeEquiv
    (fun m => m ∈ (EmbeddedMorphismFunctor.boundedEmbeddedMorphismSubfunctor jm Pm).obj (Opposite.op T))
    (fun i => i ∈ (EmbeddedMorphismFunctor.boundedEmbeddedMorphismSubfunctor ji Pi).obj (Opposite.op T))).trans
      (Intrinsic.FamilyOperationData.familyOperationDataEquiv A T).subtypeEquivOfSubtype'

def boundedFamilyOperationParameterNativeEquiv (T : Over S) :
    (T ⟶ FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi) ≃ BoundedFamilyGroupOperations jm ji Pm Pi T :=
  (FamilyOperationParameters.boundedFamilyOperationParameterPointEquiv jm ji Pm Pi T).trans
    (boundedFamilyOperationDataEquiv jm ji Pm Pi T)

def boundedFamilyUniversalOperations :
    FamilyGroup.Operations.FamilyGroupOperations ((Over.pullback (FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi).hom).obj A) :=
  (boundedFamilyOperationParameterNativeEquiv jm ji Pm Pi _ (𝟙 _)).val

theorem boundedFamilyUniversalOperations_bounded :
    ((Intrinsic.FamilyOperationData.familyOperationDataEquiv A (FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi)).symm
      (boundedFamilyUniversalOperations jm ji Pm Pi)).1.1 ∈
        (EmbeddedMorphismFunctor.boundedEmbeddedMorphismSubfunctor jm Pm).obj (Opposite.op (FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi)) ∧
    ((Intrinsic.FamilyOperationData.familyOperationDataEquiv A (FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi)).symm
      (boundedFamilyUniversalOperations jm ji Pm Pi)).1.2 ∈
        (EmbeddedMorphismFunctor.boundedEmbeddedMorphismSubfunctor ji Pi).obj (Opposite.op (FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi)) :=
  (boundedFamilyOperationParameterNativeEquiv jm ji Pm Pi _ (𝟙 _)).property

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.IntrinsicFamilyOperations
