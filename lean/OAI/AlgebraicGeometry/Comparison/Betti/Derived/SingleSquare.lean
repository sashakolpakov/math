import OAI.AlgebraicGeometry.Comparison.Betti.SingleFunctorSquare

/-! # Single Square -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Derived.SingleSquare

noncomputable section

/-! The derived square on single complexes uses the canonical coefficient maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe w₁ w₂ w₃ w₄ u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  {D : Type u₄} [Category.{v₄} D] [Abelian D] [HasDerivedCategory.{w₄} D]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (J : C ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [J.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]

def derivedSingleMap {a : A} {b : B} (f : F.obj a ⟶ b) :
    F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor A 0).obj a) ⟶
      (DerivedCategory.singleFunctor B 0).obj b :=
  (F.mapDerivedCategorySingleFunctor 0).hom.app a ≫ (DerivedCategory.singleFunctor B 0).map f

theorem derivedSingleMap_square (e : F ⋙ G ≅ H ⋙ J)
    {a : A} {b : B} {c : C} {d : D}
    (f : F.obj a ⟶ b) (g : G.obj b ⟶ d) (h : H.obj a ⟶ c) (j : J.obj c ⟶ d)
    (hs : J.map h ≫ j = e.inv.app a ≫ G.map f ≫ g) :
    J.mapDerivedCategory.map (derivedSingleMap H h) ≫ derivedSingleMap J j =
      (FunctorSquare.squareIso F G H J e).inv.app ((DerivedCategory.singleFunctor A 0).obj a) ≫
        G.mapDerivedCategory.map (derivedSingleMap F f) ≫ derivedSingleMap G g := by
  have hq := ComplexSquare.derivedComplexMap_square F G H J e
    (SingleFunctorSquare.Derived.cochainSingleMap F f) (SingleFunctorSquare.Derived.cochainSingleMap G g) (SingleFunctorSquare.Derived.cochainSingleMap H h) (SingleFunctorSquare.Derived.cochainSingleMap J j)
    (SingleFunctorSquare.Derived.cochainSingleMap_square F G H J e f g h j hs)
  erw [SingleFunctorSquare.Derived.derivedComplexMap_single, SingleFunctorSquare.Derived.derivedComplexMap_single,
    SingleFunctorSquare.Derived.derivedComplexMap_single, SingleFunctorSquare.Derived.derivedComplexMap_single] at hq
  exact hq

end

end OAI.AlgebraicGeometry.Comparison.Betti.Derived.SingleSquare
