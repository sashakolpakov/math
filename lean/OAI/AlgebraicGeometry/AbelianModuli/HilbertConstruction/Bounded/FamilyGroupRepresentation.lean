import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FamilyGroupPointClassification
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FamilyOperationFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.LawsBaseChange

/-! # Family Group Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FamilyGroupRepresentation

noncomputable section

/-! The actual bounded commutative-group operation functor, with geometric base change on all test schemes, is represented by the specified quasi-projective closed group-law parameter. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

local instance groupFunctorProductProper {S : Scheme.{u}} (X Y : Over S) [IsProper X.hom] [IsProper Y.hom] :
    IsProper (X ⊗ Y).hom := inferInstanceAs (IsProper (pullback.fst X.hom Y.hom ≫ X.hom))

local instance groupFunctorProductSmooth {S : Scheme.{u}} (X Y : Over S) [Smooth X.hom] [Smooth Y.hom] :
    Smooth (X ⊗ Y).hom := inferInstanceAs (Smooth (pullback.fst X.hom Y.hom ≫ X.hom))

variable {S : Scheme.{u}} [IsNoetherian S] {A : Over S} [IsProper A.hom] [Smooth A.hom]
variable {nm ni : ℕ} (jm : (A ⊗ A) ⊗ A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S nm)
variable (ji : A ⊗ A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S ni)
variable [IsClosedImmersion jm.left] [IsClosedImmersion ji.left] (Pm Pi : Polynomial ℚ)

def boundedFamilyGroupSubfunctor : Subfunctor (FamilyOperationFunctor.boundedFamilyOperationFunctor jm ji Pm Pi) where
  obj _ := {D | D.val.Laws}
  map f D h := D.val.geometricBaseChange_laws f.unop h

def boundedFamilyGroupFunctor : (Over S)ᵒᵖ ⥤ Type u :=
  (boundedFamilyGroupSubfunctor jm ji Pm Pi).toFunctor

theorem boundedFamilyGroupParameterNativeEquiv_val (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation A) (T : Over S)
    (y : T ⟶ FamilyGroupParameter.boundedFamilyGroupParameter jm ji Pm Pi Q) :
    (FamilyGroupPointClassification.boundedFamilyGroupParameterNativeEquiv jm ji Pm Pi Q T y).val =
      IntrinsicFamilyOperations.boundedFamilyOperationParameterNativeEquiv jm ji Pm Pi T
        (y ≫ FamilyGroupParameter.boundedFamilyGroupParameterInclusion jm ji Pm Pi Q) := rfl

def boundedFamilyGroupClassifyingIso (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation A) :
    yoneda.obj (FamilyGroupParameter.boundedFamilyGroupParameter jm ji Pm Pi Q) ≅ boundedFamilyGroupFunctor jm ji Pm Pi :=
  NatIso.ofComponents (fun T => (FamilyGroupPointClassification.boundedFamilyGroupParameterNativeEquiv jm ji Pm Pi Q T.unop).toIso) (by
    intro T U f
    apply ConcreteCategory.hom_ext
    intro y
    apply Subtype.ext
    change (FamilyGroupPointClassification.boundedFamilyGroupParameterNativeEquiv jm ji Pm Pi Q U.unop (f.unop ≫ y)).val =
      FamilyOperationFunctor.boundedFamilyOperationPullback jm ji Pm Pi f.unop
        (FamilyGroupPointClassification.boundedFamilyGroupParameterNativeEquiv jm ji Pm Pi Q T.unop y).val
    rw [boundedFamilyGroupParameterNativeEquiv_val, boundedFamilyGroupParameterNativeEquiv_val,
      FamilyOperationFunctor.boundedFamilyOperationPullback_point]
    exact congrArg (IntrinsicFamilyOperations.boundedFamilyOperationParameterNativeEquiv jm ji Pm Pi U.unop) (Category.assoc _ _ _))

theorem boundedFamilyGroup_isRepresentable (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation A) :
    (boundedFamilyGroupFunctor jm ji Pm Pi).IsRepresentable :=
  Functor.IsRepresentable.mk' (boundedFamilyGroupClassifyingIso jm ji Pm Pi Q)

theorem boundedFamilyGroup_quasiProjective_representation (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation A) :
    ∃ Z : Over S, Nonempty (Projective.ProjectivePresentations.QuasiProjectivePresentation Z) ∧
      Nonempty (boundedFamilyGroupFunctor jm ji Pm Pi ≅ yoneda.obj Z) :=
  ⟨FamilyGroupParameter.boundedFamilyGroupParameter jm ji Pm Pi Q,
    ⟨FamilyGroupParameter.boundedFamilyGroupParameterQuasiProjectivePresentation jm ji Pm Pi Q⟩,
    ⟨(boundedFamilyGroupClassifyingIso jm ji Pm Pi Q).symm⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FamilyGroupRepresentation
