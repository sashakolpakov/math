import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalCoefficientComposition
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.InverseCoordinateHomology

/-! # Coefficient Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientNaturality.CechPresheafCoefficientNaturality

noncomputable section

/-! The original Cech total coefficient isomorphism is natural in
actual maps of presheaf complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v a b d e
variable {C : Type u} [Category.{v} C]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type d} [Category.{e} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  (F : A ⥤ B) [F.Additive] (E : SimplicialObject (FormalCoproduct.{0} C))
  (hE : ∀ n, Finite (E.obj (op n)).I)
  {K L : CochainComplex (Cᵒᵖ ⥤ A) ℕ} (a : K ⟶ L)

def bicomplexMap : CoefficientTotal.CechPresheafCoefficientTotal.bicomplex E K ⟶ CoefficientTotal.CechPresheafCoefficientTotal.bicomplex E L :=
  ((FormalCoproduct.cochainComplexFunctor E).mapHomologicalComplex (.up ℕ)).map a

def totalMap := HomologicalComplex₂.total.map (bicomplexMap E a) (.up ℕ)

omit [HasCoproducts.{0} A] [HasCoproducts.{0} B] in
theorem bicomplex : TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap F (bicomplexMap E a) ≫
    (CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso F E hE L).hom =
      (CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso F E hE K).hom ≫
        bicomplexMap E (((CoefficientTotal.CechPresheafCoefficientTotal.presheaves F).mapHomologicalComplex (.up ℕ)).map a) :=
  (NatIso.mapHomologicalComplex (GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.iso F E hE) (.up ℕ)).hom.naturality a

theorem total : (F.mapHomologicalComplex (.up ℕ)).map (totalMap E a) ≫
    (CoefficientTotal.CechPresheafCoefficientTotal.totalIso F E hE L).hom =
      (CoefficientTotal.CechPresheafCoefficientTotal.totalIso F E hE K).hom ≫
        totalMap E (((CoefficientTotal.CechPresheafCoefficientTotal.presheaves F).mapHomologicalComplex (.up ℕ)).map a) := by
  have h₁ := IntegralComparison.InverseCoordinateHomology.inverse
    (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F (CoefficientTotal.CechPresheafCoefficientTotal.bicomplex E K))
    (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F (CoefficientTotal.CechPresheafCoefficientTotal.bicomplex E L))
    (HomologicalComplex₂.total.map (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap F (bicomplexMap E a)) (.up ℕ))
    ((F.mapHomologicalComplex (.up ℕ)).map (totalMap E a))
    (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.natural F (bicomplexMap E a))
  let T := HomologicalComplex₂.totalFunctor B (.up ℕ) (.up ℕ) (.up ℕ)
  have h₂ := (T.map_comp (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap F (bicomplexMap E a))
    (CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso F E hE L).hom).symm.trans
      ((congrArg T.map (bicomplex F E hE a)).trans
        (T.map_comp (CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso F E hE K).hom
          (bicomplexMap E (((CoefficientTotal.CechPresheafCoefficientTotal.presheaves F).mapHomologicalComplex (.up ℕ)).map a))))
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientNaturality.CechPresheafCoefficientNaturality
