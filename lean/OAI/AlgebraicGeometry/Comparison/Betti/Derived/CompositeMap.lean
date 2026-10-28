import OAI.AlgebraicGeometry.Comparison.Betti.Derived.SingleSquare

/-! # Composite Map -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Derived.CompositeMap

noncomputable section

/-! A canonical comparison with a composite exact functor preserves actual cochain maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe w₁ w₂ w₃ u₁ u₂ u₃ v₁ v₂ v₃

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
  [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

def compositeIso (e : F ⋙ G ≅ H) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory :=
  FunctorComposition.derivedFunctorCompIso F G ≪≫ FunctorIso.functorIso e

instance compositeIsoCommShift (e : F ⋙ G ≅ H) : NatTrans.CommShift (compositeIso F G H e).hom ℤ := by
  change NatTrans.CommShift ((FunctorComposition.derivedFunctorCompIso F G).hom ≫ (FunctorIso.functorIso e).hom) ℤ
  infer_instance

theorem compositeIso_hom_app (e : F ⋙ G ≅ H) (K : CochainComplex A ℤ) :
    (compositeIso F G H e).hom.app (DerivedCategory.Q.obj K) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app K) ≫
            H.mapDerivedCategoryFactors.inv.app K := by
  change (FunctorComposition.derivedFunctorCompIso F G).hom.app (DerivedCategory.Q.obj K) ≫
    (FunctorIso.functorIso e).hom.app (DerivedCategory.Q.obj K) = _
  erw [FunctorComposition.derivedFunctorCompIso_hom_app_explicit, FunctorIso.functorIso_hom_app]
  simp only [Category.assoc]
  simp only [Iso.inv_hom_id_app_assoc]

theorem derivedComplexMap_comp (e : F ⋙ G ≅ H)
    {K : CochainComplex A ℤ} {L : CochainComplex B ℤ} {M : CochainComplex C ℤ}
    (f : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ L)
    (g : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L ⟶ M)
    (h : (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ M)
    (hs : (G.mapHomologicalComplex (ComplexShape.up ℤ)).map f ≫ g =
      (NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app K ≫ h) :
    G.mapDerivedCategory.map (ResolutionNaturality.Ext.derivedComplexMap F f) ≫ ResolutionNaturality.Ext.derivedComplexMap G g =
      (compositeIso F G H e).hom.app (DerivedCategory.Q.obj K) ≫ ResolutionNaturality.Ext.derivedComplexMap H h := by
  let Q : CochainComplex C ℤ ⥤ DerivedCategory C := DerivedCategory.Q
  let a := G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K)
  let b := G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  let c := G.mapDerivedCategoryFactors.app L
  let d := H.mapDerivedCategoryFactors.app K
  let x := G.mapDerivedCategory.map (DerivedCategory.Q.map f)
  let y := Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
  let z := Q.map ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app K)
  have hn : x ≫ c.hom = b.hom ≫ y := G.mapDerivedCategoryFactors_hom_naturality f
  have hq : y ≫ Q.map g = z ≫ Q.map h :=
    (Q.map_comp _ _).symm.trans ((Q.congr_map hs).trans (Q.map_comp _ _))
  erw [compositeIso_hom_app]
  change G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map f) ≫
    (c.hom ≫ Q.map g) = (a ≫ b.hom ≫ z ≫ d.inv) ≫ (d.hom ≫ Q.map h)
  erw [G.mapDerivedCategory.map_comp]
  change (a ≫ x) ≫ (c.hom ≫ Q.map g) = (a ≫ b.hom ≫ z ≫ d.inv) ≫ (d.hom ≫ Q.map h)
  simp only [Category.assoc]
  rw [← Category.assoc x c.hom, hn]
  simp only [Category.assoc]
  rw [hq]
  erw [d.inv_hom_id_assoc]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Derived.CompositeMap
