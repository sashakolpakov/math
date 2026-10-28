import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductCoefficient
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalProductReindex
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.CoefficientNaturality

/-! # Total Product Reindex Coefficient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalProductReindexCoefficient.CechConeTotalProductReindexCoefficient

noncomputable section

/-! The canonical total coefficient comparison commutes with tuple
reindexing along a functor preserving the actual products. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v uD vD w z w' z'
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type uD} [Category.{vD} D] [Quiver.IsThin D] [HasBinaryProducts D]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type w'} [Category.{z'} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  (F : C ⥤ D) (G : A ⥤ B) [G.Additive] {ι : Type} [Finite ι] (U : ι → C)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  (P : Dᵒᵖ ⥤ CochainComplex A ℕ)

local instance finiteBiproducts : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts

omit [HasCoproducts.{0} A] [HasCoproducts.{0} B] in
theorem bicomplex : TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap G
    (TotalProductReindex.CechConeTotalProductReindex.bicomplexIso F U P).hom ≫
      (TotalCoefficient.CechConeTotalCoefficient.bicomplexIso G (F.obj ∘ U) P).hom =
    (TotalCoefficient.CechConeTotalCoefficient.bicomplexIso G U (F.op ⋙ P)).hom ≫
      (TotalProductReindex.CechConeTotalProductReindex.bicomplexIso F U (TotalCoefficient.CechConeTotalCoefficient.mapped G P)).hom := by
  exact congrArg (HomologicalComplex₂.flipFunctor B (.up ℕ) (.up ℕ)).map
    (NonemptyCech.ProductCoefficient.NonemptyCechProductCoefficient.natural F (G.mapHomologicalComplex (.up ℕ)) U P)

theorem total : (G.mapHomologicalComplex (.up ℕ)).map (TotalProductReindex.CechConeTotalProductReindex.iso F U P).hom ≫
    (TotalCoefficient.CechConeTotalCoefficient.totalIso G (F.obj ∘ U) P).hom =
      (TotalCoefficient.CechConeTotalCoefficient.totalIso G U (F.op ⋙ P)).hom ≫
        (TotalProductReindex.CechConeTotalProductReindex.iso F U (TotalCoefficient.CechConeTotalCoefficient.mapped G P)).hom := by
  let a := (TotalProductReindex.CechConeTotalProductReindex.bicomplexIso F U P).hom
  have h₁ := IntegralComparison.InverseCoordinateHomology.inverse
    (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G (Total.CechConeTotal.bicomplex U (F.op ⋙ P)))
    (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G (Total.CechConeTotal.bicomplex (F.obj ∘ U) P))
    (HomologicalComplex₂.total.map (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap G a) (.up ℕ))
    ((G.mapHomologicalComplex (.up ℕ)).map (TotalProductReindex.CechConeTotalProductReindex.iso F U P).hom)
    (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.natural G a)
  let T := HomologicalComplex₂.totalFunctor B (.up ℕ) (.up ℕ) (.up ℕ)
  have h₂ := (T.map_comp (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap G a)
    (TotalCoefficient.CechConeTotalCoefficient.bicomplexIso G (F.obj ∘ U) P).hom).symm.trans
      ((congrArg T.map (bicomplex F G U P)).trans
        (T.map_comp (TotalCoefficient.CechConeTotalCoefficient.bicomplexIso G U (F.op ⋙ P)).hom
          (TotalProductReindex.CechConeTotalProductReindex.bicomplexIso F U (TotalCoefficient.CechConeTotalCoefficient.mapped G P)).hom))
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalProductReindexCoefficient.CechConeTotalProductReindexCoefficient
