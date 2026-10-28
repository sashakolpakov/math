import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.RefinementCoefficient
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalRefinement
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.CoefficientNaturality

/-! # Total Refinement Coefficient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalRefinementCoefficient.CechConeTotalRefinementCoefficient

noncomputable section

/-! The original finite total coefficient comparison commutes with
actual Cech refinement of the covering family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z w' z'
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type w'} [Category.{z'} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  (F : A ⥤ B) [F.Additive] {ι κ : Type} [Finite ι] [Finite κ] (U : ι → C) (V : κ → C)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  (P : Cᵒᵖ ⥤ CochainComplex A ℕ)

local instance finiteBiproducts : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts

omit [HasCoproducts.{0} A] [HasCoproducts.{0} B] in
theorem bicomplex : TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap F (TotalRefinement.CechConeTotalRefinement.bicomplexMap U V r P) ≫
    (TotalCoefficient.CechConeTotalCoefficient.bicomplexIso F V P).hom =
      (TotalCoefficient.CechConeTotalCoefficient.bicomplexIso F U P).hom ≫
        TotalRefinement.CechConeTotalRefinement.bicomplexMap U V r (TotalCoefficient.CechConeTotalCoefficient.mapped F P) := by
  have h := congrArg (HomologicalComplex₂.flipFunctor B (.up ℕ) (.up ℕ)).map
    (NonemptyCech.RefinementCoefficient.NonemptyCechRefinementCoefficient.natural (F.mapHomologicalComplex (.up ℕ)) U V r P)
  exact h

theorem total : (F.mapHomologicalComplex (.up ℕ)).map (TotalRefinement.CechConeTotalRefinement.map U V r P) ≫
    (TotalCoefficient.CechConeTotalCoefficient.totalIso F V P).hom =
      (TotalCoefficient.CechConeTotalCoefficient.totalIso F U P).hom ≫
        TotalRefinement.CechConeTotalRefinement.map U V r (TotalCoefficient.CechConeTotalCoefficient.mapped F P) := by
  let a := TotalRefinement.CechConeTotalRefinement.bicomplexMap U V r P
  have h₁ := IntegralComparison.InverseCoordinateHomology.inverse
    (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso F (Total.CechConeTotal.bicomplex U P))
    (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso F (Total.CechConeTotal.bicomplex V P))
    (HomologicalComplex₂.total.map (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap F a) (.up ℕ))
    ((F.mapHomologicalComplex (.up ℕ)).map (TotalRefinement.CechConeTotalRefinement.map U V r P))
    (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.natural F a)
  let T := HomologicalComplex₂.totalFunctor B (.up ℕ) (.up ℕ) (.up ℕ)
  have h₂ := (T.map_comp (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap F a)
    (TotalCoefficient.CechConeTotalCoefficient.bicomplexIso F V P).hom).symm.trans
      ((congrArg T.map (bicomplex F U V r P)).trans
        (T.map_comp (TotalCoefficient.CechConeTotalCoefficient.bicomplexIso F U P).hom
          (TotalRefinement.CechConeTotalRefinement.bicomplexMap U V r (TotalCoefficient.CechConeTotalCoefficient.mapped F P))))
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalRefinementCoefficient.CechConeTotalRefinementCoefficient
