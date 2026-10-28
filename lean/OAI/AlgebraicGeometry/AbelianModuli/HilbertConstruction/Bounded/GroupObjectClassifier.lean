import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FamilyGroupPointClassification
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.GraphHilbertBaseChange

/-! # Group Object Classifier -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A proper smooth commutative group whose actual multiplication and
inversion graphs satisfy fixed Hilbert conditions supplies points of the
existing bounded group-law parameter on every test scheme. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

attribute [local irreducible] Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding

section

def FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj {S : Scheme.{u}} (X : Over S) [GrpObj X] : FamilyGroup.Operations.FamilyGroupOperations X where
  unit := η[X]
  mul := μ[X]
  inv := ι[X]

theorem FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj_laws {S : Scheme.{u}} (X : Over S) [GrpObj X] [IsCommMonObj X] :
    (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj X).Laws :=
  ⟨MonObj.one_mul X, MonObj.mul_one X, MonObj.mul_assoc X,
    GrpObj.left_inv X, GrpObj.right_inv X, IsCommMonObj.mul_comm X⟩
end

local instance Bounded.GroupObjectClassifier.classifierPullbackSeparated {S T : Scheme.{u}} (X : Over S) [IsSeparated X.hom] (b : T ⟶ S) :
    IsSeparated ((Over.pullback b).obj X).hom := inferInstanceAs (IsSeparated (pullback.snd X.hom b))

local instance Bounded.GroupObjectClassifier.classifierPullbackFlat {S T : Scheme.{u}} (X : Over S) [Flat X.hom] (b : T ⟶ S) :
    Flat ((Over.pullback b).obj X).hom := inferInstanceAs (Flat (pullback.snd X.hom b))

local instance Bounded.GroupObjectClassifier.classifierPullbackFinitePresentation {S T : Scheme.{u}} (X : Over S)
    [LocallyOfFinitePresentation X.hom] (b : T ⟶ S) :
    LocallyOfFinitePresentation ((Over.pullback b).obj X).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (pullback.snd X.hom b))

local instance Bounded.GroupObjectClassifier.classifierProductFlat {S : Scheme.{u}} (X Y : Over S) [Flat X.hom] [Flat Y.hom] :
    Flat (X ⊗ Y).hom := inferInstanceAs (Flat (pullback.fst X.hom Y.hom ≫ X.hom))

local instance Bounded.GroupObjectClassifier.classifierProductFinitePresentation {S : Scheme.{u}} (X Y : Over S)
    [LocallyOfFinitePresentation X.hom] [LocallyOfFinitePresentation Y.hom] :
    LocallyOfFinitePresentation (X ⊗ Y).hom := inferInstanceAs
      (LocallyOfFinitePresentation (pullback.fst X.hom Y.hom ≫ X.hom))

variable {S : Scheme.{u}} [IsNoetherian S] {A : Over S}
variable [IsProper A.hom] [Smooth A.hom] [GrpObj A] [IsCommMonObj A]
variable {nm ni : ℕ} (jm : (A ⊗ A) ⊗ A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S nm)
variable (ji : A ⊗ A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S ni)
variable [IsClosedImmersion jm.left] [IsClosedImmersion ji.left] (Pm Pi : Polynomial ℚ)
variable (hm : Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial jm Pm μ[A])
variable (hi : Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial ji Pi ι[A])

def Bounded.GroupObjectClassifier.boundedGroupObjectOperations (T : Over S) : Bounded.FamilyGroupPointClassification.BoundedCommutativeFamilyGroupOperations jm ji Pm Pi T := by
  let D := FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj ((Over.pullback T.hom).obj A)
  refine ⟨⟨D, ?_, ?_⟩, FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj_laws _⟩
  · change Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom jm) Pm
      ((Functor.Monoidal.μIso (Over.pullback T.hom) A A).inv ≫ μ[(Over.pullback T.hom).obj A])
    have hmul : (Functor.Monoidal.μIso (Over.pullback T.hom) A A).inv ≫
        μ[(Over.pullback T.hom).obj A] = (Over.pullback T.hom).map μ[A] := by
      change (Functor.Monoidal.μIso (Over.pullback T.hom) A A).inv ≫
        ((Functor.Monoidal.μIso (Over.pullback T.hom) A A).hom ≫ (Over.pullback T.hom).map μ[A]) = _
      exact Iso.inv_hom_id_assoc _ _
    have hb := Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial.baseChange jm Pm hm T.hom
    exact hmul.symm ▸ hb
  · change Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom ji) Pi
      ((Over.pullback T.hom).map ι[A])
    exact Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial.baseChange ji Pi hi T.hom

variable (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation A)

def Bounded.GroupObjectClassifier.boundedGroupObjectClassifier (T : Over S) : T ⟶ Bounded.FamilyGroupParameter.boundedFamilyGroupParameter jm ji Pm Pi Q :=
  (Bounded.FamilyGroupPointClassification.boundedFamilyGroupParameterNativeEquiv jm ji Pm Pi Q T).symm
    (Bounded.GroupObjectClassifier.boundedGroupObjectOperations jm ji Pm Pi hm hi T)

theorem Bounded.GroupObjectClassifier.boundedGroupObjectClassifier_operations (T : Over S) :
    Bounded.FamilyGroupPointClassification.boundedFamilyGroupParameterNativeEquiv jm ji Pm Pi Q T
      (Bounded.GroupObjectClassifier.boundedGroupObjectClassifier jm ji Pm Pi hm hi Q T) =
        Bounded.GroupObjectClassifier.boundedGroupObjectOperations jm ji Pm Pi hm hi T :=
  (Bounded.FamilyGroupPointClassification.boundedFamilyGroupParameterNativeEquiv jm ji Pm Pi Q T).apply_symm_apply _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
