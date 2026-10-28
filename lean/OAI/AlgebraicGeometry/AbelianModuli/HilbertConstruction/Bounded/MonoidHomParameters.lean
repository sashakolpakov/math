import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.MonoidHomUniversalMorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.MonoidHomParameters

/-! # Monoid Hom Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.MonoidHomParameters

noncomputable section

/-! Morphisms between proper smooth group families that preserve identity and multiplication and have a prescribed graph polynomial are classified by a concrete quasi-projective closed parameter. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.Obj

universe u

local instance monoidParameterPullbackProper {S T : Scheme.{u}} (c : T ⟶ S) (X : Over S) [IsProper X.hom] :
    IsProper ((Over.pullback c).obj X).hom := inferInstanceAs (IsProper (pullback.snd X.hom c))

local instance monoidParameterPullbackFlat {S T : Scheme.{u}} (c : T ⟶ S) (X : Over S) [Flat X.hom] :
    Flat ((Over.pullback c).obj X).hom := inferInstanceAs (Flat (pullback.snd X.hom c))

local instance monoidParameterPullbackSeparated {S T : Scheme.{u}} (c : T ⟶ S) (X : Over S) [IsSeparated X.hom] :
    IsSeparated ((Over.pullback c).obj X).hom := inferInstanceAs (IsSeparated (pullback.snd X.hom c))

variable {S : Scheme.{u}} [IsNoetherian S] {A B : Over S} {n : ℕ}
variable [IsProper A.hom] [Smooth A.hom] [IsSeparated B.hom] [MonObj A] [MonObj B]
variable (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (P : Polynomial ℚ)

local instance monoidGraphParameterNoetherian : IsLocallyNoetherian (HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameter j P).left :=
  (HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameterQuasiProjectivePresentation j P).noetherian.toIsLocallyNoetherian

def boundedFamilyMonoidHomParameter : Over S :=
  Family.MonoidHomParameters.familyMonoidHomParameter (HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameter j P) (MonoidHomUniversalMorphism.boundedEmbeddedUniversalNativeMorphism j P)

def boundedFamilyMonoidHomParameterInclusion : boundedFamilyMonoidHomParameter j P ⟶ HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameter j P :=
  Family.MonoidHomParameters.familyMonoidHomParameterInclusion _ (MonoidHomUniversalMorphism.boundedEmbeddedUniversalNativeMorphism j P)

instance boundedFamilyMonoidHomParameterInclusion_closed :
    IsClosedImmersion (boundedFamilyMonoidHomParameterInclusion j P).left :=
  Family.MonoidHomParameters.familyMonoidHomParameterInclusion_closed _ (MonoidHomUniversalMorphism.boundedEmbeddedUniversalNativeMorphism j P)

def boundedFamilyMonoidHomParameterQuasiProjectivePresentation :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (boundedFamilyMonoidHomParameter j P) :=
  Family.MonoidHomParameters.familyMonoidHomParameterQuasiProjectivePresentation _ (MonoidHomUniversalMorphism.boundedEmbeddedUniversalNativeMorphism j P)
    (HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameterQuasiProjectivePresentation j P)

def BoundedFamilyMonoidHom (T : Over S) :=
  {f : (EmbeddedMorphismFunctor.boundedEmbeddedMorphismFunctor j P).obj (Opposite.op T) // IsMonHom f.val}

def boundedFamilyMonoidHomParameterPointEquiv (T : Over S) :
    (T ⟶ boundedFamilyMonoidHomParameter j P) ≃ BoundedFamilyMonoidHom j P T :=
  (Family.MonoidHomParameters.familyMonoidHomParameterPointEquiv _ (MonoidHomUniversalMorphism.boundedEmbeddedUniversalNativeMorphism j P) T).trans
    ((HilbertConstruction.Smooth.GraphParameterPointEquivalence.smoothEmbeddedGraphParameterMorphismEquiv j P T).subtypeEquiv
      (fun y => (MonoidHomUniversalMorphism.boundedEmbeddedUniversalNativeMorphism_monHom_iff j P y).symm))

theorem boundedFamilyMonoidHomParameterPointEquiv_val (T : Over S)
    (y : T ⟶ boundedFamilyMonoidHomParameter j P) :
    (boundedFamilyMonoidHomParameterPointEquiv j P T y).val =
      HilbertConstruction.Smooth.GraphParameterPointEquivalence.smoothEmbeddedGraphParameterMorphismEquiv j P T (y ≫ boundedFamilyMonoidHomParameterInclusion j P) := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.MonoidHomParameters
