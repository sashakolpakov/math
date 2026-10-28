import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalCoefficient
import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalCoefficientComposition
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.InverseCoordinateHomology

/-! # Coefficient Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.CoefficientNaturality.CechConeCoefficientNaturality

noncomputable section

/-! The original finite Cech total coefficient isomorphism is natural in
maps of complex-valued diagrams. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z w' z'
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type w'} [Category.{z'} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  (F : A ⥤ B) [F.Additive] {ι : Type} [Finite ι] (U : ι → C)
  {P Q : Cᵒᵖ ⥤ CochainComplex A ℕ} (a : P ⟶ Q)

local instance finiteBiproducts : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts

def bicomplexMap : Total.CechConeTotal.bicomplex U P ⟶ Total.CechConeTotal.bicomplex U Q :=
  (HomologicalComplex₂.flipFunctor A (.up ℕ) (.up ℕ)).map ((IntegralComparison.NonemptyCechNerve.complexFunctor U).map a)

omit [HasCoproducts.{0} A] [HasCoproducts.{0} B] in
theorem bicomplex : TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap F (bicomplexMap U a) ≫
    (TotalCoefficient.CechConeTotalCoefficient.bicomplexIso F U Q).hom =
      (TotalCoefficient.CechConeTotalCoefficient.bicomplexIso F U P).hom ≫
        bicomplexMap U (Functor.whiskerRight a (F.mapHomologicalComplex (.up ℕ))) := by
  have h := congrArg (HomologicalComplex₂.flipFunctor B (.up ℕ) (.up ℕ)).map
    (GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.naturality (F.mapHomologicalComplex (.up ℕ))
      (IntegralComparison.NonemptyCechNerve.nerve U) (TotalCoefficient.CechConeTotalCoefficient.finite_indices U) a)
  simp only [Functor.map_comp] at h
  exact h

theorem total : (F.mapHomologicalComplex (.up ℕ)).map ((TotalFunctor.CechConeTotalFunctor.functor U).map a) ≫
    (TotalCoefficient.CechConeTotalCoefficient.totalIso F U Q).hom =
      (TotalCoefficient.CechConeTotalCoefficient.totalIso F U P).hom ≫
        (TotalFunctor.CechConeTotalFunctor.functor U).map (Functor.whiskerRight a (F.mapHomologicalComplex (.up ℕ))) := by
  have h₁ := IntegralComparison.InverseCoordinateHomology.inverse
    (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso F (Total.CechConeTotal.bicomplex U P))
    (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso F (Total.CechConeTotal.bicomplex U Q))
    (HomologicalComplex₂.total.map (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap F (bicomplexMap U a)) (.up ℕ))
    ((F.mapHomologicalComplex (.up ℕ)).map ((TotalFunctor.CechConeTotalFunctor.functor U).map a))
    (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.natural F (bicomplexMap U a))
  let T := HomologicalComplex₂.totalFunctor B (.up ℕ) (.up ℕ) (.up ℕ)
  have h₂ := (T.map_comp (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap F (bicomplexMap U a))
    (TotalCoefficient.CechConeTotalCoefficient.bicomplexIso F U Q).hom).symm.trans
      ((congrArg T.map (bicomplex F U a)).trans
        (T.map_comp (TotalCoefficient.CechConeTotalCoefficient.bicomplexIso F U P).hom
          (bicomplexMap U (Functor.whiskerRight a (F.mapHomologicalComplex (.up ℕ))))))
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.CoefficientNaturality.CechConeCoefficientNaturality
