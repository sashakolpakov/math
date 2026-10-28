import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.OperationParameterNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackMonoidIso

/-! # Monoid Hom Universal Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.MonoidHomUniversalMorphism

noncomputable section

/-! The bounded morphism parameter has a native universal morphism; its group-homomorphism condition agrees with the closed equation test on every parameter point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} [IsNoetherian S] {A B : Over S} {n : ℕ}
variable [IsProper A.hom] [Smooth A.hom] [IsSeparated B.hom]
variable (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (P : Polynomial ℚ)

def boundedEmbeddedUniversalNativeMorphism :
    (Over.pullback (HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameter j P).hom).obj A ⟶
      (Over.pullback (HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameter j P).hom).obj B :=
  (HilbertConstruction.Smooth.GraphParameterPointEquivalence.smoothEmbeddedGraphParameterMorphismEquiv j P _ (𝟙 _)).val

theorem boundedEmbeddedUniversalNativeMorphism_point {T : Over S}
    (y : T ⟶ HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameter j P) :
    (HilbertConstruction.Smooth.GraphParameterPointEquivalence.smoothEmbeddedGraphParameterMorphismEquiv j P T y).val =
      Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange y (boundedEmbeddedUniversalNativeMorphism j P) := by
  have h := OperationParameterNaturality.smoothEmbeddedGraphParameterMorphismEquiv_natural j P y (𝟙 _)
  rw [Category.comp_id] at h
  exact congrArg Subtype.val h

theorem boundedEmbeddedUniversalNativeMorphism_monHom_iff [MonObj A] [MonObj B]
    {T : Over S} (y : T ⟶ HilbertConstruction.Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameter j P) :
    IsMonHom (HilbertConstruction.Smooth.GraphParameterPointEquivalence.smoothEmbeddedGraphParameterMorphismEquiv j P T y).val ↔
      IsMonHom ((Over.pullback y.left).map (boundedEmbeddedUniversalNativeMorphism j P)) := by
  rw [boundedEmbeddedUniversalNativeMorphism_point]
  exact ParameterPullbackMonoidIso.geometricFamilyMorphismBaseChange_isMonHom_iff y (boundedEmbeddedUniversalNativeMorphism j P)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.MonoidHomUniversalMorphism
