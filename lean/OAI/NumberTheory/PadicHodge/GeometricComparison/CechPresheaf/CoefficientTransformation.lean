import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CechCoefficientTransformation

/-! # Coefficient Transformation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientTransformation.CechPresheafCoefficientTransformation

noncomputable section

/-! Changing coefficient functors commutes with original finite Cech
totalization of presheaf complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v a b d e
variable {C : Type u} [Category.{v} C]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type d} [Category.{e} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  (F G : A ⥤ B) [F.Additive] [G.Additive] (α : F ⟶ G)
  (E : SimplicialObject (FormalCoproduct.{0} C)) (hE : ∀ n, Finite (E.obj (op n)).I)
  (K : CochainComplex (Cᵒᵖ ⥤ A) ℕ)

def presheaves : CoefficientTotal.CechPresheafCoefficientTotal.presheaves (C := C) F ⟶ CoefficientTotal.CechPresheafCoefficientTotal.presheaves G :=
  (Functor.whiskeringRight Cᵒᵖ A B).map α

def complexes : CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex F K ⟶ CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex G K :=
  ((presheaves F G α).mapHomologicalComplex (.up ℕ)).app K

omit [HasCoproducts.{0} A] [HasCoproducts.{0} B] in
theorem bicomplex : TotalCoefficientComposition.TotalCoefficientComparisonNaturality.coefficientMap F G α (CoefficientTotal.CechPresheafCoefficientTotal.bicomplex E K) ≫
    (CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso G E hE K).hom =
    (CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso F E hE K).hom ≫
      CoefficientNaturality.CechPresheafCoefficientNaturality.bicomplexMap E (complexes F G α K) := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact GeometricComparison.Finite.CechCoefficientTransformation.FiniteCechCoefficientTransformation.complexes F G α E hE (K.X i)

theorem total : (α.mapHomologicalComplex (.up ℕ)).app ((CoefficientTotal.CechPresheafCoefficientTotal.bicomplex E K).total (.up ℕ)) ≫
    (CoefficientTotal.CechPresheafCoefficientTotal.totalIso G E hE K).hom =
    (CoefficientTotal.CechPresheafCoefficientTotal.totalIso F E hE K).hom ≫
      CoefficientNaturality.CechPresheafCoefficientNaturality.totalMap E (complexes F G α K) := by
  have h₁ := IntegralComparison.InverseCoordinateHomology.inverse
    (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F (CoefficientTotal.CechPresheafCoefficientTotal.bicomplex E K))
    (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso G (CoefficientTotal.CechPresheafCoefficientTotal.bicomplex E K))
    (HomologicalComplex₂.total.map (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.coefficientMap F G α
      (CoefficientTotal.CechPresheafCoefficientTotal.bicomplex E K)) (.up ℕ))
    ((α.mapHomologicalComplex (.up ℕ)).app ((CoefficientTotal.CechPresheafCoefficientTotal.bicomplex E K).total (.up ℕ)))
    (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.coefficients F G α (CoefficientTotal.CechPresheafCoefficientTotal.bicomplex E K))
  let T := HomologicalComplex₂.totalFunctor B (.up ℕ) (.up ℕ) (.up ℕ)
  have h₂ := (T.map_comp (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.coefficientMap F G α (CoefficientTotal.CechPresheafCoefficientTotal.bicomplex E K))
    (CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso G E hE K).hom).symm.trans
      ((congrArg T.map (bicomplex F G α E hE K)).trans
        (T.map_comp (CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso F E hE K).hom
          (CoefficientNaturality.CechPresheafCoefficientNaturality.bicomplexMap E (complexes F G α K))))
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientTransformation.CechPresheafCoefficientTransformation
