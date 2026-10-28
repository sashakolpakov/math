import OAI.AlgebraicGeometry.Comparison.Betti.Derived.FunctorComposition
import OAI.AlgebraicGeometry.Comparison.Betti.Derived.FunctorIso

/-! # Functor Square -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Derived.FunctorSquare

noncomputable section

/-! Normalization of a constructed square of exact functors in the derived category. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

private theorem inverseFive {V : Type*} [Category* V] {A B C D E F : V}
    (a : A ≅ B) (b : B ≅ C) (q : C ≅ D) (c : E ≅ D) (d : F ≅ E) :
    (a ≪≫ b ≪≫ q ≪≫ c.symm ≪≫ d.symm).inv = d.hom ≫ c.hom ≫ q.inv ≫ b.inv ≫ a.inv := by
  change (((d.hom ≫ c.hom) ≫ q.inv) ≫ b.inv) ≫ a.inv = _
  simp only [Category.assoc]

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
  (e : F ⋙ G ≅ H ⋙ J)

def squareIso : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
    H.mapDerivedCategory ⋙ J.mapDerivedCategory :=
  FunctorComposition.derivedFunctorCompIso F G ≪≫ FunctorIso.functorIso e ≪≫ (FunctorComposition.derivedFunctorCompIso H J).symm

theorem squareIso_hom_app (K : CochainComplex A ℤ) :
    (squareIso F G H J e).hom.app (DerivedCategory.Q.obj K) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app K) ≫
            J.mapDerivedCategoryFactors.inv.app ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
              J.mapDerivedCategory.map (H.mapDerivedCategoryFactors.inv.app K) := by
  change (FunctorComposition.derivedFunctorCompIso F G).hom.app (DerivedCategory.Q.obj K) ≫
      (FunctorIso.functorIso e).hom.app (DerivedCategory.Q.obj K) ≫
      (FunctorComposition.derivedFunctorCompIso H J).inv.app (DerivedCategory.Q.obj K) = _
  erw [FunctorComposition.derivedFunctorCompIso_hom_app_explicit F G K, FunctorIso.functorIso_hom_app e K,
    FunctorComposition.derivedFunctorCompIso_inv_app_explicit H J K]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

theorem squareIso_inv_app (K : CochainComplex A ℤ) :
    (squareIso F G H J e).inv.app (DerivedCategory.Q.obj K) =
      J.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
        J.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.inv (ComplexShape.up ℤ)).app K) ≫
            G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
              G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) := by
  let a := G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app K)
  let b := G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  let q := DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).app K)
  let c := J.mapDerivedCategoryFactors.app ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  let d := J.mapDerivedCategory.mapIso (H.mapDerivedCategoryFactors.app K)
  let r := (squareIso F G H J e).app (DerivedCategory.Q.obj K)
  have hr : r.hom = a.hom ≫ b.hom ≫ q.hom ≫ c.inv ≫ d.inv := squareIso_hom_app F G H J e K
  change r.inv = d.hom ≫ c.hom ≫ q.inv ≫ b.inv ≫ a.inv
  have he : r = a ≪≫ b ≪≫ q ≪≫ c.symm ≪≫ d.symm := Iso.ext hr
  exact (congrArg Iso.inv he).trans (inverseFive a b q c d)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Derived.FunctorSquare
