import OAI.AlgebraicGeometry.Comparison.Betti.Derived.ComplexSquare

/-! # Single Functor Square -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SingleFunctorSquare.Derived

noncomputable section

/-! Canonical maps on single complexes preserve a square of coefficient maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

section Cochains

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]

def cochainSingleMap (F : A ⥤ B) [F.Additive] {a : A} {b : B} (f : F.obj a ⟶ b) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((CochainComplex.singleFunctor A 0).obj a) ⟶
      (CochainComplex.singleFunctor B 0).obj b :=
  (F.mapCochainComplexSingleFunctor 0).hom.app a ≫ (CochainComplex.singleFunctor B 0).map f

theorem cochainSingleMap_f_zero (F : A ⥤ B) [F.Additive] {a : A} {b : B} (f : F.obj a ⟶ b) :
    (cochainSingleMap F f).f 0 =
      F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 a).hom ≫ f ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 b).inv := by
  change ((F.mapCochainComplexSingleFunctor 0).hom.app a).f 0 ≫
    ((CochainComplex.singleFunctor B 0).map f).f 0 = _
  erw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single_map_f_self]
  let sa := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 a
  let sfa := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (F.obj a)
  let sb := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 b
  change (F.map sa.hom ≫ sfa.inv) ≫ (sfa.hom ≫ f ≫ sb.inv) = F.map sa.hom ≫ f ≫ sb.inv
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

theorem cochainSingleMap_square (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (J : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [J.Additive] (e : F ⋙ G ≅ H ⋙ J)
    {a : A} {b : B} {c : C} {d : D}
    (f : F.obj a ⟶ b) (g : G.obj b ⟶ d) (h : H.obj a ⟶ c) (j : J.obj c ⟶ d)
    (hs : J.map h ≫ j = e.inv.app a ≫ G.map f ≫ g) :
    (J.mapHomologicalComplex (ComplexShape.up ℤ)).map (cochainSingleMap H h) ≫ cochainSingleMap J j =
      (NatTrans.mapHomologicalComplex e.inv (ComplexShape.up ℤ)).app
          ((CochainComplex.singleFunctor A 0).obj a) ≫
        (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (cochainSingleMap F f) ≫ cochainSingleMap G g := by
  apply HomologicalComplex.to_single_hom_ext
  change J.map ((cochainSingleMap H h).f 0) ≫ (cochainSingleMap J j).f 0 =
    e.inv.app (((CochainComplex.singleFunctor A 0).obj a).X 0) ≫
      G.map ((cochainSingleMap F f).f 0) ≫ (cochainSingleMap G g).f 0
  rw [cochainSingleMap_f_zero, cochainSingleMap_f_zero,
    cochainSingleMap_f_zero, cochainSingleMap_f_zero]
  let sa := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 a
  let sb := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 b
  let sc := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 c
  let sd := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 d
  change J.map (H.map sa.hom ≫ h ≫ sc.inv) ≫ (J.map sc.hom ≫ j ≫ sd.inv) =
    e.inv.app _ ≫ G.map (F.map sa.hom ≫ f ≫ sb.inv) ≫ (G.map sb.hom ≫ g ≫ sd.inv)
  simp only [J.map_comp, G.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc]
  rw [← Category.assoc (J.map h) j, hs]
  have hn : J.map (H.map sa.hom) ≫ e.inv.app a =
      e.inv.app _ ≫ G.map (F.map sa.hom) := e.inv.naturality sa.hom
  simp only [Category.assoc]
  rw [← Category.assoc (J.map (H.map sa.hom)) (e.inv.app a), hn]
  simp only [Category.assoc]

end Cochains

universe w w' u u' v v'

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

theorem derivedComplexMap_single {a : A} {b : B} (f : F.obj a ⟶ b) :
    Derived.ResolutionNaturality.Ext.derivedComplexMap F (cochainSingleMap F f) =
      (F.mapDerivedCategorySingleFunctor 0).hom.app a ≫ (DerivedCategory.singleFunctor B 0).map f := by
  let K := (CochainComplex.singleFunctor A 0).obj a
  let Q : CochainComplex B ℤ ⥤ DerivedCategory B := DerivedCategory.Q
  have h := F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app a
  have hh : F.mapDerivedCategoryFactors.hom.app K ≫
      Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app a) =
        (F.mapDerivedCategorySingleFunctor 0).hom.app a := by
    rw [← h]
    let i := F.mapDerivedCategoryFactors.app K
    let k := (F.mapDerivedCategorySingleFunctor 0).hom.app a
    change i.hom ≫ (i.inv ≫ k) = k
    exact i.hom_inv_id_assoc k
  change F.mapDerivedCategoryFactors.hom.app K ≫
    Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app a ≫
      (CochainComplex.singleFunctor B 0).map f) = _
  rw [Q.map_comp, ← Category.assoc, hh]
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.SingleFunctorSquare.Derived
