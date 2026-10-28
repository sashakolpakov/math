import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Adjunction

/-! # Exact Derived -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ExactDerived.ExactDerivedAdjunction

noncomputable section

/-! # Passing an exact additive adjunction to actual derived categories -/

open _root_.CategoryTheory

universe u₁ u₂ v₁ v₂ w₁ w₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {F : C ⥤ D} [F.Additive] {G : D ⥤ C} [G.Additive] (adj : F ⊣ G)

def onComplexes : F.mapHomologicalComplex (ComplexShape.up ℤ) ⊣
    G.mapHomologicalComplex (ComplexShape.up ℤ) where
  unit :=
    { app := fun K =>
        { f := fun i => adj.unit.app (K.X i)
          comm' := fun i j _ => (adj.unit.naturality (K.d i j)).symm }
      naturality := fun K L φ => by
        apply HomologicalComplex.Hom.ext
        funext i
        exact adj.unit.naturality (φ.f i) }
  counit :=
    { app := fun K =>
        { f := fun i => adj.counit.app (K.X i)
          comm' := fun i j _ => (adj.counit.naturality (K.d i j)).symm }
      naturality := fun K L φ => by
        apply HomologicalComplex.Hom.ext
        funext i
        exact adj.counit.naturality (φ.f i) }
  left_triangle_components K := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact adj.left_triangle_components (K.X i)
  right_triangle_components K := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact adj.right_triangle_components (K.X i)

variable [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]

def map (F : C ⥤ D) [F.Additive] [F.PreservesHomology] : DerivedCategory C ⥤ DerivedCategory D :=
  F.mapHomologicalComplexUpToQuasiIso (ComplexShape.up ℤ)

def mapFactors (F : C ⥤ D) [F.Additive] [F.PreservesHomology] :
    DerivedCategory.Q ⋙ map F ≅ F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  F.mapHomologicalComplexUpToQuasiIsoFactors (ComplexShape.up ℤ)

def onDerived [F.PreservesHomology] [G.PreservesHomology] : map F ⊣ map G := by
  letI : CatCommSq (F.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q (C := C)) (DerivedCategory.Q (C := D)) (map F) :=
    ⟨(mapFactors F).symm⟩
  letI : CatCommSq (G.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q (C := D)) (DerivedCategory.Q (C := C)) (map G) :=
    ⟨(mapFactors G).symm⟩
  exact (onComplexes adj).localization DerivedCategory.Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) (map F) (map G)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ExactDerived.ExactDerivedAdjunction
