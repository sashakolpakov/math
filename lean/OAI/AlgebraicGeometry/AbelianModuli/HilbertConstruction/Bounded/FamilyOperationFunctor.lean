import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.OperationParameterNaturality

/-! # Family Operation Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FamilyOperationFunctor

noncomputable section

/-! Bounded native family operations form a functor under actual geometric base change, naturally represented by the concrete product parameter. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

local instance operationFunctorProductProper {S : Scheme.{u}} (X Y : Over S) [IsProper X.hom] [IsProper Y.hom] :
    IsProper (X ⊗ Y).hom := inferInstanceAs (IsProper (pullback.fst X.hom Y.hom ≫ X.hom))

local instance operationFunctorProductSmooth {S : Scheme.{u}} (X Y : Over S) [Smooth X.hom] [Smooth Y.hom] :
    Smooth (X ⊗ Y).hom := inferInstanceAs (Smooth (pullback.fst X.hom Y.hom ≫ X.hom))

variable {S : Scheme.{u}} [IsNoetherian S] {A : Over S} [IsProper A.hom] [Smooth A.hom]
variable {nm ni : ℕ} (jm : (A ⊗ A) ⊗ A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S nm)
variable (ji : A ⊗ A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S ni)
variable [IsClosedImmersion jm.left] [IsClosedImmersion ji.left] (Pm Pi : Polynomial ℚ)

def boundedFamilyOperationPullback {U T : Over S} (f : U ⟶ T)
    (D : IntrinsicFamilyOperations.BoundedFamilyGroupOperations jm ji Pm Pi T) : IntrinsicFamilyOperations.BoundedFamilyGroupOperations jm ji Pm Pi U := by
  refine ⟨D.val.geometricBaseChange f, ?_⟩
  have h := OperationParameterNaturality.boundedFamilyOperationParameterNativeEquiv_natural jm ji Pm Pi f
    ((IntrinsicFamilyOperations.boundedFamilyOperationParameterNativeEquiv jm ji Pm Pi T).symm D)
  rw [Equiv.apply_symm_apply] at h
  rw [← h]
  exact (IntrinsicFamilyOperations.boundedFamilyOperationParameterNativeEquiv jm ji Pm Pi U
    (f ≫ (IntrinsicFamilyOperations.boundedFamilyOperationParameterNativeEquiv jm ji Pm Pi T).symm D)).property

theorem boundedFamilyOperationPullback_point {U T : Over S} (f : U ⟶ T)
    (y : T ⟶ FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi) :
    boundedFamilyOperationPullback jm ji Pm Pi f (IntrinsicFamilyOperations.boundedFamilyOperationParameterNativeEquiv jm ji Pm Pi T y) =
      IntrinsicFamilyOperations.boundedFamilyOperationParameterNativeEquiv jm ji Pm Pi U (f ≫ y) := by
  apply Subtype.ext
  exact (OperationParameterNaturality.boundedFamilyOperationParameterNativeEquiv_natural jm ji Pm Pi f y).symm

def boundedFamilyOperationFunctor : (Over S)ᵒᵖ ⥤ Type u where
  obj T := IntrinsicFamilyOperations.BoundedFamilyGroupOperations jm ji Pm Pi T.unop
  map f := TypeCat.ofHom (boundedFamilyOperationPullback jm ji Pm Pi f.unop)
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro D
    obtain ⟨y, rfl⟩ := (IntrinsicFamilyOperations.boundedFamilyOperationParameterNativeEquiv jm ji Pm Pi T.unop).surjective D
    change boundedFamilyOperationPullback jm ji Pm Pi (𝟙 T.unop)
      (IntrinsicFamilyOperations.boundedFamilyOperationParameterNativeEquiv jm ji Pm Pi T.unop y) = _
    rw [boundedFamilyOperationPullback_point, Category.id_comp]
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro D
    obtain ⟨y, rfl⟩ := (IntrinsicFamilyOperations.boundedFamilyOperationParameterNativeEquiv jm ji Pm Pi _).surjective D
    change boundedFamilyOperationPullback jm ji Pm Pi (g.unop ≫ f.unop)
      (IntrinsicFamilyOperations.boundedFamilyOperationParameterNativeEquiv jm ji Pm Pi _ y) =
      boundedFamilyOperationPullback jm ji Pm Pi g.unop
        (boundedFamilyOperationPullback jm ji Pm Pi f.unop
          (IntrinsicFamilyOperations.boundedFamilyOperationParameterNativeEquiv jm ji Pm Pi _ y))
    rw [boundedFamilyOperationPullback_point, boundedFamilyOperationPullback_point,
      boundedFamilyOperationPullback_point]
    exact congrArg (IntrinsicFamilyOperations.boundedFamilyOperationParameterNativeEquiv jm ji Pm Pi _) (Category.assoc _ _ _)

def boundedFamilyOperationClassifyingIso :
    yoneda.obj (FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi) ≅ boundedFamilyOperationFunctor jm ji Pm Pi :=
  NatIso.ofComponents (fun T => (IntrinsicFamilyOperations.boundedFamilyOperationParameterNativeEquiv jm ji Pm Pi T.unop).toIso) (by
    intro T U f
    apply ConcreteCategory.hom_ext
    intro y
    exact (boundedFamilyOperationPullback_point jm ji Pm Pi f.unop y).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FamilyOperationFunctor
