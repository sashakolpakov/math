import OAI.AlgebraicGeometry.Comparison.Betti.Derived.FunctorSquare
import OAI.AlgebraicGeometry.Comparison.Betti.Derived.ResolutionNaturality

/-! # Complex Square -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Derived.ComplexSquare

noncomputable section

/-! Transport an actual square of cochain maps through exact derived functors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

private theorem pasteDerivedSquare {V : Type*} [Category* V]
    {S A B C D E F G H I T : V}
    (a : S ⟶ A) (b : A ≅ B) (y : A ⟶ C) (j : C ≅ D) (p : D ⟶ T)
    (u : B ⟶ D) (q : B ⟶ E) (d : F ≅ E) (c : G ≅ F) (x : F ⟶ H)
    (k : H ≅ I) (r : I ⟶ T) (v : E ⟶ I)
    (hy : y ≫ j.hom = b.hom ≫ u) (hx : x ≫ k.hom = d.hom ≫ v)
    (hq : u ≫ p = q ≫ v ≫ r) :
    (a ≫ y) ≫ j.hom ≫ p =
      (a ≫ b.hom ≫ q ≫ d.inv ≫ c.inv) ≫ (c.hom ≫ x) ≫ k.hom ≫ r := by
  calc
    (a ≫ y) ≫ j.hom ≫ p = a ≫ b.hom ≫ u ≫ p := by
      rw [Category.assoc, ← Category.assoc y j.hom, hy]
      simp only [Category.assoc]
    _ = a ≫ b.hom ≫ q ≫ v ≫ r := by
      exact congrArg (fun t => a ≫ b.hom ≫ t) hq
    _ = (a ≫ b.hom ≫ q ≫ d.inv ≫ c.inv) ≫ (c.hom ≫ x) ≫ k.hom ≫ r := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc x k.hom, hx]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]

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

theorem derivedComplexMap_square
    {K : CochainComplex A ℤ} {L : CochainComplex B ℤ}
    {N : CochainComplex C ℤ} {M : CochainComplex D ℤ}
    (f : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ L)
    (g : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L ⟶ M)
    (h : (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ N)
    (j : (J.mapHomologicalComplex (ComplexShape.up ℤ)).obj N ⟶ M)
    (hs : (J.mapHomologicalComplex (ComplexShape.up ℤ)).map h ≫ j =
      (NatTrans.mapHomologicalComplex e.inv (ComplexShape.up ℤ)).app K ≫
        (G.mapHomologicalComplex (ComplexShape.up ℤ)).map f ≫ g) :
    J.mapDerivedCategory.map (ResolutionNaturality.Ext.derivedComplexMap H h) ≫ ResolutionNaturality.Ext.derivedComplexMap J j =
      (FunctorSquare.squareIso F G H J e).inv.app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategory.map (ResolutionNaturality.Ext.derivedComplexMap F f) ≫ ResolutionNaturality.Ext.derivedComplexMap G g := by
  let Q : CochainComplex D ℤ ⥤ DerivedCategory D := DerivedCategory.Q
  let a := J.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K)
  let b := J.mapDerivedCategoryFactors.app ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  let y := J.mapDerivedCategory.map (DerivedCategory.Q.map h)
  let j' := J.mapDerivedCategoryFactors.app N
  let p := Q.map j
  let u := Q.map ((J.mapHomologicalComplex (ComplexShape.up ℤ)).map h)
  let q := Q.map ((NatTrans.mapHomologicalComplex e.inv (ComplexShape.up ℤ)).app K)
  let d := G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  let c := G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app K)
  let x := G.mapDerivedCategory.map (DerivedCategory.Q.map f)
  let k := G.mapDerivedCategoryFactors.app L
  let r := Q.map g
  let v := Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
  have hy : y ≫ j'.hom = b.hom ≫ u := J.mapDerivedCategoryFactors_hom_naturality h
  have hx : x ≫ k.hom = d.hom ≫ v := G.mapDerivedCategoryFactors_hom_naturality f
  have hq : u ≫ p = q ≫ v ≫ r := by
    exact (Q.map_comp _ _).symm.trans ((Q.congr_map hs).trans
      ((Q.map_comp _ _).trans (congrArg (fun t => q ≫ t) (Q.map_comp _ _))))
  erw [FunctorSquare.squareIso_inv_app F G H J e K]
  change J.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map h) ≫
      j'.hom ≫ p =
    (a ≫ b.hom ≫ q ≫ d.inv ≫ c.inv) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map f) ≫
        k.hom ≫ r
  erw [J.mapDerivedCategory.map_comp, G.mapDerivedCategory.map_comp]
  exact pasteDerivedSquare (V := DerivedCategory D) a b y j' p u q d c x k r v hy hx hq

end

end OAI.AlgebraicGeometry.Comparison.Betti.Derived.ComplexSquare
