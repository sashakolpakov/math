import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.IntrinsicFamilyOperations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.GeometricFamilyGroupOperations

/-! # Operation Parameter Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.OperationParameterNaturality

noncomputable section

/-! The actual bounded-operation point classification is natural under geometric base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

theorem familyOperationProjection_precomp {S : Scheme.{u}} {U T M V W : Over S}
    (f : U ⟶ T) (y : T ⟶ M) (a : M ⟶ V) (b : V ⟶ W) :
    ((f ≫ y) ≫ a) ≫ b = f ≫ ((y ≫ a) ≫ b) :=
  (congrArg (fun k => k ≫ b) (Category.assoc f y a)).trans (Category.assoc f (y ≫ a) b)

theorem smoothEmbeddedGraphParameterMorphismEquiv_natural
    {S : Scheme.{u}} [IsNoetherian S] {A B : Over S} {n : ℕ}
    [IsProper A.hom] [Smooth A.hom] [IsSeparated B.hom]
    (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (P : Polynomial ℚ)
    {U T : Over S} (f : U ⟶ T) (y : T ⟶ HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameter j P) :
    HilbertConstruction.Smooth.GraphParameterPointEquivalence.smoothEmbeddedGraphParameterMorphismEquiv j P U (f ≫ y) =
      (EmbeddedMorphismFunctor.boundedEmbeddedMorphismFunctor j P).map f.op (HilbertConstruction.Smooth.GraphParameterPointEquivalence.smoothEmbeddedGraphParameterMorphismEquiv j P T y) :=
  ConcreteCategory.congr_hom ((EmbeddedMorphismRepresentation.boundedEmbeddedMorphismClassifyingIso j P).symm.hom.naturality f.op) y

local instance boundedNaturalProductProper {S : Scheme.{u}} (X Y : Over S) [IsProper X.hom] [IsProper Y.hom] :
    IsProper (X ⊗ Y).hom := inferInstanceAs (IsProper (pullback.fst X.hom Y.hom ≫ X.hom))

local instance boundedNaturalProductSmooth {S : Scheme.{u}} (X Y : Over S) [Smooth X.hom] [Smooth Y.hom] :
    Smooth (X ⊗ Y).hom := inferInstanceAs (Smooth (pullback.fst X.hom Y.hom ≫ X.hom))

variable {S : Scheme.{u}} [IsNoetherian S] {A : Over S} [IsProper A.hom] [Smooth A.hom]
variable {nm ni : ℕ} (jm : (A ⊗ A) ⊗ A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S nm)
variable (ji : A ⊗ A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S ni)
variable [IsClosedImmersion jm.left] [IsClosedImmersion ji.left] (Pm Pi : Polynomial ℚ)

theorem boundedFamilyOperationParameterNativeEquiv_val (T : Over S)
    (y : T ⟶ FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi) :
    (IntrinsicFamilyOperations.boundedFamilyOperationParameterNativeEquiv jm ji Pm Pi T y).val =
      Intrinsic.FamilyOperationData.familyOperationDataEquiv A T
        (((FamilyOperationParameters.boundedFamilyOperationParameterPointEquiv jm ji Pm Pi T y).1.1.val,
          (FamilyOperationParameters.boundedFamilyOperationParameterPointEquiv jm ji Pm Pi T y).1.2.val),
          (FamilyOperationParameters.boundedFamilyOperationParameterPointEquiv jm ji Pm Pi T y).2) := rfl

theorem boundedFamilyOperationParameterPointEquiv_natural {U T : Over S} (f : U ⟶ T)
    (y : T ⟶ FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi) :
    FamilyOperationParameters.boundedFamilyOperationParameterPointEquiv jm ji Pm Pi U (f ≫ y) =
      (((EmbeddedMorphismFunctor.boundedEmbeddedMorphismFunctor jm Pm).map f.op (FamilyOperationParameters.boundedFamilyOperationParameterPointEquiv jm ji Pm Pi T y).1.1,
        (EmbeddedMorphismFunctor.boundedEmbeddedMorphismFunctor ji Pi).map f.op (FamilyOperationParameters.boundedFamilyOperationParameterPointEquiv jm ji Pm Pi T y).1.2),
        f ≫ (FamilyOperationParameters.boundedFamilyOperationParameterPointEquiv jm ji Pm Pi T y).2) := by
  apply Prod.ext
  · apply Prod.ext
    · change HilbertConstruction.Smooth.GraphParameterPointEquivalence.smoothEmbeddedGraphParameterMorphismEquiv jm Pm U (((f ≫ y) ≫ fst _ _) ≫ fst _ _) =
        (EmbeddedMorphismFunctor.boundedEmbeddedMorphismFunctor jm Pm).map f.op
          (HilbertConstruction.Smooth.GraphParameterPointEquivalence.smoothEmbeddedGraphParameterMorphismEquiv jm Pm T ((y ≫ fst _ _) ≫ fst _ _))
      exact (congrArg (HilbertConstruction.Smooth.GraphParameterPointEquivalence.smoothEmbeddedGraphParameterMorphismEquiv jm Pm U)
        (familyOperationProjection_precomp f y (fst _ _) (fst _ _))).trans
          (smoothEmbeddedGraphParameterMorphismEquiv_natural jm Pm f
            ((y ≫ fst (HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameter jm Pm ⊗ HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameter ji Pi) A) ≫ fst _ _))
    · change HilbertConstruction.Smooth.GraphParameterPointEquivalence.smoothEmbeddedGraphParameterMorphismEquiv ji Pi U (((f ≫ y) ≫ fst _ _) ≫ snd _ _) =
        (EmbeddedMorphismFunctor.boundedEmbeddedMorphismFunctor ji Pi).map f.op
          (HilbertConstruction.Smooth.GraphParameterPointEquivalence.smoothEmbeddedGraphParameterMorphismEquiv ji Pi T ((y ≫ fst _ _) ≫ snd _ _))
      exact (congrArg (HilbertConstruction.Smooth.GraphParameterPointEquivalence.smoothEmbeddedGraphParameterMorphismEquiv ji Pi U)
        (familyOperationProjection_precomp f y (fst _ _) (snd _ _))).trans
          (smoothEmbeddedGraphParameterMorphismEquiv_natural ji Pi f
            ((y ≫ fst (HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameter jm Pm ⊗ HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameter ji Pi) A) ≫ snd _ _))
  · exact Category.assoc f y (snd _ _)

theorem boundedFamilyOperationParameterNativeEquiv_natural {U T : Over S} (f : U ⟶ T)
    (y : T ⟶ FamilyOperationParameters.boundedFamilyOperationParameter jm ji Pm Pi) :
    (IntrinsicFamilyOperations.boundedFamilyOperationParameterNativeEquiv jm ji Pm Pi U (f ≫ y)).val =
      (IntrinsicFamilyOperations.boundedFamilyOperationParameterNativeEquiv jm ji Pm Pi T y).val.geometricBaseChange f := by
  rw [boundedFamilyOperationParameterNativeEquiv_val, boundedFamilyOperationParameterNativeEquiv_val,
    boundedFamilyOperationParameterPointEquiv_natural]
  exact (Geometric.GeometricFamilyGroupOperations.familyOperationData_geometricBaseChange f _ _ _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.OperationParameterNaturality
