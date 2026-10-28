import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.CoefficientNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CechCoefficientTransformation

/-! # Coefficient Transformation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.CoefficientTransformation.CechConeCoefficientTransformation

noncomputable section

/-! Natural transformations of additive coefficient functors commute
with the original finite Cech total coefficient isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z w' z'
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type w'} [Category.{z'} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  (F G : A ⥤ B) [F.Additive] [G.Additive] (α : F ⟶ G)
  {ι : Type} [Finite ι] (U : ι → C) (P : Cᵒᵖ ⥤ CochainComplex A ℕ)

local instance finiteBiproducts : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts

omit [HasCoproducts.{0} A] [HasCoproducts.{0} B] in
theorem bicomplex : TotalCoefficientComposition.TotalCoefficientComparisonNaturality.coefficientMap F G α (Total.CechConeTotal.bicomplex U P) ≫
    (TotalCoefficient.CechConeTotalCoefficient.bicomplexIso G U P).hom =
      (TotalCoefficient.CechConeTotalCoefficient.bicomplexIso F U P).hom ≫
        CoefficientNaturality.CechConeCoefficientNaturality.bicomplexMap U (Functor.whiskerLeft P (α.mapHomologicalComplex (.up ℕ))) := by
  have h := congrArg (HomologicalComplex₂.flipFunctor B (.up ℕ) (.up ℕ)).map
    (GeometricComparison.Finite.CechCoefficientTransformation.FiniteCechCoefficientTransformation.complexes (F.mapHomologicalComplex (.up ℕ))
      (G.mapHomologicalComplex (.up ℕ)) (α.mapHomologicalComplex (.up ℕ))
      (IntegralComparison.NonemptyCechNerve.nerve U) (TotalCoefficient.CechConeTotalCoefficient.finite_indices U) P)
  simp only [Functor.map_comp] at h
  exact h

theorem total : (α.mapHomologicalComplex (.up ℕ)).app (Total.CechConeTotal.total U P) ≫
    (TotalCoefficient.CechConeTotalCoefficient.totalIso G U P).hom =
      (TotalCoefficient.CechConeTotalCoefficient.totalIso F U P).hom ≫
        (TotalFunctor.CechConeTotalFunctor.functor U).map (Functor.whiskerLeft P (α.mapHomologicalComplex (.up ℕ))) := by
  have h₁ := IntegralComparison.InverseCoordinateHomology.inverse
    (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso F (Total.CechConeTotal.bicomplex U P))
    (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G (Total.CechConeTotal.bicomplex U P))
    (HomologicalComplex₂.total.map (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.coefficientMap F G α
      (Total.CechConeTotal.bicomplex U P)) (.up ℕ))
    ((α.mapHomologicalComplex (.up ℕ)).app (Total.CechConeTotal.total U P))
    (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.coefficients F G α (Total.CechConeTotal.bicomplex U P))
  let T := HomologicalComplex₂.totalFunctor B (.up ℕ) (.up ℕ) (.up ℕ)
  have h₂ := (T.map_comp (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.coefficientMap F G α (Total.CechConeTotal.bicomplex U P))
    (TotalCoefficient.CechConeTotalCoefficient.bicomplexIso G U P).hom).symm.trans
      ((congrArg T.map (bicomplex F G α U P)).trans
        (T.map_comp (TotalCoefficient.CechConeTotalCoefficient.bicomplexIso F U P).hom
          (CoefficientNaturality.CechConeCoefficientNaturality.bicomplexMap U (Functor.whiskerLeft P (α.mapHomologicalComplex (.up ℕ))))))
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.CoefficientTransformation.CechConeCoefficientTransformation
