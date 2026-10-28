import OAI.AlgebraicGeometry.Comparison.Betti.Derived.CompositeMap

/-! # Single Composition -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Derived.SingleComposition

noncomputable section

/-! Composition of the canonical coefficient maps on single complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

section Cochains

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C]

theorem cochainSingleMap_comp (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H)
    {a : A} {b : B} {c : C} (f : F.obj a ⟶ b) (g : G.obj b ⟶ c) (h : H.obj a ⟶ c)
    (hs : G.map f ≫ g = e.hom.app a ≫ h) :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (SingleFunctorSquare.Derived.cochainSingleMap F f) ≫ SingleFunctorSquare.Derived.cochainSingleMap G g =
      (NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app
          ((CochainComplex.singleFunctor A 0).obj a) ≫ SingleFunctorSquare.Derived.cochainSingleMap H h := by
  apply HomologicalComplex.to_single_hom_ext
  change G.map ((SingleFunctorSquare.Derived.cochainSingleMap F f).f 0) ≫ (SingleFunctorSquare.Derived.cochainSingleMap G g).f 0 =
    e.hom.app (((CochainComplex.singleFunctor A 0).obj a).X 0) ≫ (SingleFunctorSquare.Derived.cochainSingleMap H h).f 0
  rw [SingleFunctorSquare.Derived.cochainSingleMap_f_zero, SingleFunctorSquare.Derived.cochainSingleMap_f_zero, SingleFunctorSquare.Derived.cochainSingleMap_f_zero]
  let sa := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 a
  let sb := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 b
  let sc := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 c
  change G.map (F.map sa.hom ≫ f ≫ sb.inv) ≫ (G.map sb.hom ≫ g ≫ sc.inv) =
    e.hom.app _ ≫ H.map sa.hom ≫ h ≫ sc.inv
  simp only [G.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc]
  rw [← Category.assoc (G.map f) g, hs]
  have hn : G.map (F.map sa.hom) ≫ e.hom.app a = e.hom.app _ ≫ H.map sa.hom :=
    e.hom.naturality sa.hom
  simp only [Category.assoc]
  rw [← Category.assoc (G.map (F.map sa.hom)) (e.hom.app a), hn]
  simp only [Category.assoc]

end Cochains

universe w₁ w₂ w₃ u₁ u₂ u₃ v₁ v₂ v₃

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
  [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

theorem derivedSingleMap_comp (e : F ⋙ G ≅ H)
    {a : A} {b : B} {c : C} (f : F.obj a ⟶ b) (g : G.obj b ⟶ c) (h : H.obj a ⟶ c)
    (hs : G.map f ≫ g = e.hom.app a ≫ h) :
    G.mapDerivedCategory.map (SingleSquare.derivedSingleMap F f) ≫ SingleSquare.derivedSingleMap G g =
      (CompositeMap.compositeIso F G H e).hom.app ((DerivedCategory.singleFunctor A 0).obj a) ≫ SingleSquare.derivedSingleMap H h := by
  have hq := CompositeMap.derivedComplexMap_comp F G H e
    (SingleFunctorSquare.Derived.cochainSingleMap F f) (SingleFunctorSquare.Derived.cochainSingleMap G g) (SingleFunctorSquare.Derived.cochainSingleMap H h)
    (cochainSingleMap_comp F G H e f g h hs)
  erw [SingleFunctorSquare.Derived.derivedComplexMap_single, SingleFunctorSquare.Derived.derivedComplexMap_single, SingleFunctorSquare.Derived.derivedComplexMap_single] at hq
  exact hq

end

end OAI.AlgebraicGeometry.Comparison.Betti.Derived.SingleComposition
