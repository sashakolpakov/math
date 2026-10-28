import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedMapParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedMapBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.MonoidHomUniversalMorphism

/-! # Pointed Map Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PointedMapParameters

noncomputable section

/-! Bounded identity-preserving family morphisms are classified by a concrete closed subscheme of the smooth graph parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

local instance pointedBoundedPullbackSeparated {S T : Scheme.{u}} (c : T ⟶ S) (X : Over S)
    [IsSeparated X.hom] : IsSeparated ((Over.pullback c).obj X).hom :=
  inferInstanceAs (IsSeparated (Limits.pullback.snd X.hom c))

variable {S : Scheme.{u}} [IsNoetherian S] {A B : Over S} {n : ℕ}
variable [IsProper A.hom] [Smooth A.hom] [IsSeparated B.hom] [MonObj A] [MonObj B]
variable (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (P : Polynomial ℚ)

local instance pointedBoundedParameterNoetherian : IsLocallyNoetherian (HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameter j P).left :=
  (HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameterQuasiProjectivePresentation j P).noetherian.toIsLocallyNoetherian

theorem boundedEmbeddedUniversalNativeMorphism_pointed_iff {T : Over S}
    (y : T ⟶ HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameter j P) :
    η[(Over.pullback T.hom).obj A] ≫ (HilbertConstruction.Smooth.GraphParameterPointEquivalence.smoothEmbeddedGraphParameterMorphismEquiv j P T y).val =
        η[(Over.pullback T.hom).obj B] ↔
      η[(Over.pullback y.left).obj ((Over.pullback (HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameter j P).hom).obj A)] ≫
          (Over.pullback y.left).map (MonoidHomUniversalMorphism.boundedEmbeddedUniversalNativeMorphism j P) =
        η[(Over.pullback y.left).obj ((Over.pullback (HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameter j P).hom).obj B)] := by
  rw [MonoidHomUniversalMorphism.boundedEmbeddedUniversalNativeMorphism_point]
  exact PointedMapBaseChange.geometricFamilyMorphismBaseChange_pointed_iff y (MonoidHomUniversalMorphism.boundedEmbeddedUniversalNativeMorphism j P)

def boundedPointedMapParameter : Over S :=
  PointedMapParameters.pointedMapParameter (HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameter j P) (MonoidHomUniversalMorphism.boundedEmbeddedUniversalNativeMorphism j P)

def boundedPointedMapParameterInclusion : boundedPointedMapParameter j P ⟶ HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameter j P :=
  PointedMapParameters.pointedMapParameterInclusion _ (MonoidHomUniversalMorphism.boundedEmbeddedUniversalNativeMorphism j P)

instance boundedPointedMapParameterInclusion_closed : IsClosedImmersion (boundedPointedMapParameterInclusion j P).left :=
  PointedMapParameters.pointedMapParameterInclusion_closed _ (MonoidHomUniversalMorphism.boundedEmbeddedUniversalNativeMorphism j P)

def boundedPointedMapParameterQuasiProjectivePresentation : Projective.ProjectivePresentations.QuasiProjectivePresentation (boundedPointedMapParameter j P) :=
  PointedMapParameters.pointedMapParameterQuasiProjectivePresentation _ (MonoidHomUniversalMorphism.boundedEmbeddedUniversalNativeMorphism j P)
    (HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameterQuasiProjectivePresentation j P)

def BoundedFamilyPointedMap (T : Over S) :=
  {f : (EmbeddedMorphismFunctor.boundedEmbeddedMorphismFunctor j P).obj (.op T) //
    η[(Over.pullback T.hom).obj A] ≫ f.val = η[(Over.pullback T.hom).obj B]}

def boundedPointedMapParameterPointEquiv (T : Over S) :
    (T ⟶ boundedPointedMapParameter j P) ≃ BoundedFamilyPointedMap j P T :=
  (PointedMapParameters.pointedMapParameterPointEquiv _ (MonoidHomUniversalMorphism.boundedEmbeddedUniversalNativeMorphism j P) T).trans
    ((HilbertConstruction.Smooth.GraphParameterPointEquivalence.smoothEmbeddedGraphParameterMorphismEquiv j P T).subtypeEquiv
      (fun y => (boundedEmbeddedUniversalNativeMorphism_pointed_iff j P y).symm))

theorem boundedPointedMapParameterPointEquiv_val (T : Over S) (y : T ⟶ boundedPointedMapParameter j P) :
    (boundedPointedMapParameterPointEquiv j P T y).val =
      HilbertConstruction.Smooth.GraphParameterPointEquivalence.smoothEmbeddedGraphParameterMorphismEquiv j P T (y ≫ boundedPointedMapParameterInclusion j P) := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PointedMapParameters
