import Mathlib

/-! # Adjunction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Complex.Adjunction

/-! Lifting the actual adjunctions used in BettiComparison to complexes, degree by degree. -/

open _root_.CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  {F : C ⥤ D} [F.Additive] {G : D ⥤ C} [G.Additive]
  (adj : F ⊣ G) {ι : Type*} (c : ComplexShape ι)

def onComplexes : F.mapHomologicalComplex c ⊣ G.mapHomologicalComplex c where
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

end OAI.AlgebraicGeometry.Comparison.Betti.Complex.Adjunction
