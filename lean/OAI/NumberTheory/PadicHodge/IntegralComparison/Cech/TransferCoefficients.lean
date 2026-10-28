import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.BaseChangeCoefficients
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.OpenBaseChangeNaturality

/-! # Transfer Coefficients -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TransferCoefficients

noncomputable section

/-! A genuine presheaf transfer on inverse-image Čech complexes
commutes with coefficient change and with coefficient isomorphisms. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private theorem inverse_square {E : Type*} [Category E] {A B C D : E}
    (e : A ≅ B) (f : C ≅ D) (a : A ⟶ C) (b : B ⟶ D)
    (h : e.hom ≫ b = a ≫ f.hom) : e.inv ≫ a = b ≫ f.inv := by
  apply (cancel_epi e.hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

universe w v vD vA vB u uD uA uB
variable {A : Type uA} [Category.{vA} A] [Preadditive A] [HasProducts.{w} A]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasProducts.{w} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{w,w} G]
  {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {D : Type uD} [Category.{vD} D] [Quiver.IsThin D] [HasFiniteProducts D]
  (F : C ⥤ D) [PreservesFiniteLimits F] {ι : Type w} (U : ι → C)
  {P : Dᵒᵖ ⥤ A} {Q : Cᵒᵖ ⥤ A} (a : F.op ⋙ P ⟶ Q)

theorem base_inverse :
    (G.mapHomologicalComplex (.up ℕ)).map (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U P).inv ≫
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk ι U).cech (F.op ⋙ P)).hom =
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk ι (F.obj ∘ U)).cech P).hom ≫
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U (P ⋙ G)).inv :=
  inverse_square
    ((G.mapHomologicalComplex (.up ℕ)).mapIso (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U P))
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U (P ⋙ G))
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk ι U).cech (F.op ⋙ P)).hom
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk ι (F.obj ∘ U)).cech P).hom
    (BaseChangeCoefficients.naturality G F U P)

theorem naturality :
    (G.mapHomologicalComplex (.up ℕ)).map
      ((AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U P).inv ≫ (cechComplexFunctor U).map a) ≫
        (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk ι U).cech Q).hom =
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk ι (F.obj ∘ U)).cech P).hom ≫
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U (P ⋙ G)).inv ≫
        (cechComplexFunctor U).map (Functor.whiskerRight a G) := by
  let H := G.mapHomologicalComplex (.up ℕ)
  let l := (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U P).inv
  let m := (cechComplexFunctor U).map a
  let c := (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk ι U).cech Q).hom
  let d := (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk ι U).cech (F.op ⋙ P)).hom
  let t := (cechComplexFunctor U).map (Functor.whiskerRight a G)
  have h : H.map m ≫ c = d ≫ t :=
    AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.naturality G (FormalCoproduct.mk ι U).cech a
  exact (congrArg (fun z => z ≫ c) (H.map_comp l m)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => H.map l ≫ z) h).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ t) (base_inverse G F U (P := P))).trans
            (Category.assoc _ _ _)))))

omit G [Preadditive B] [HasProducts.{w} B] [G.Additive] [PreservesLimitsOfSize.{w,w} G] in
theorem conjugate {P₀ : Dᵒᵖ ⥤ A} {Q₀ : Cᵒᵖ ⥤ A}
    (e : P₀ ≅ P) (s : Q₀ ≅ Q) :
    (cechComplexFunctor (F.obj ∘ U)).map e.hom ≫
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U P).inv ≫ (cechComplexFunctor U).map a ≫
        (cechComplexFunctor U).map s.inv =
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U P₀).inv ≫
      (cechComplexFunctor U).map (Functor.whiskerLeft F.op e.hom ≫ a ≫ s.inv) := by
  have h := AlgebraicGeometry.Crystalline.Cohomology.Cech.OpenBaseChangeNaturality.CechOpenBaseChangeNaturality.naturality F U e.hom
  have he : (cechComplexFunctor (F.obj ∘ U)).map e.hom ≫
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U P).inv =
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U P₀).inv ≫
      (cechComplexFunctor U).map (Functor.whiskerLeft F.op e.hom) := by
    apply (cancel_epi (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U P₀).hom).1
    rw [← Category.assoc, ← h]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [Functor.map_comp]
  rw [← Category.assoc, he]
  simp only [Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TransferCoefficients
