import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.CoefficientNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CechCoefficientComposition
import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalCoefficient

/-! # Coefficient Composition -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.CoefficientComposition.CechConeCoefficientComposition

noncomputable section

/-! Original finite Cech total coefficient isomorphisms respect
composition of additive coefficient functors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

private theorem fourFactors {V : Type*} [Category* V] {A B C D E F : V}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (d : D ⟶ E) (e : B ⟶ F) (f : F ⟶ D)
    (h : b ≫ c = e ≫ f) : (a ≫ b) ≫ (c ≫ d) = (a ≫ e) ≫ (f ≫ d) := by
  rw [Category.assoc, ← Category.assoc b, h]
  simp only [Category.assoc]

universe u v w z w' z' w'' z''
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type w'} [Category.{z'} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  {D : Type w''} [Category.{z''} D] [Abelian D] [HasProducts.{0} D] [HasCoproducts.{0} D]
  (F : A ⥤ B) [F.Additive] (G : B ⥤ D) [G.Additive]
  {ι : Type} [Finite ι] (U : ι → C) (P : Cᵒᵖ ⥤ CochainComplex A ℕ)

local instance finiteBiproductsA : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts
local instance finiteBiproductsB : HasFiniteBiproducts B := HasFiniteBiproducts.of_hasFiniteProducts

omit [HasCoproducts.{0} A] [HasCoproducts.{0} B] [HasCoproducts.{0} D] in
theorem bicomplex : (TotalCoefficient.CechConeTotalCoefficient.bicomplexIso (F ⋙ G) U P).hom =
    TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap G (TotalCoefficient.CechConeTotalCoefficient.bicomplexIso F U P).hom ≫
      (TotalCoefficient.CechConeTotalCoefficient.bicomplexIso G U (TotalCoefficient.CechConeTotalCoefficient.mapped F P)).hom :=
  (congrArg (HomologicalComplex₂.flipFunctor D (.up ℕ) (.up ℕ)).map
    (GeometricComparison.Finite.CechCoefficientComposition.FiniteCechCoefficientComposition.complexes (F.mapHomologicalComplex (.up ℕ))
      (G.mapHomologicalComplex (.up ℕ)) (IntegralComparison.NonemptyCechNerve.nerve U)
      (TotalCoefficient.CechConeTotalCoefficient.finite_indices U) P)).trans
    ((HomologicalComplex₂.flipFunctor D (.up ℕ) (.up ℕ)).map_comp _ _)

theorem total : (TotalCoefficient.CechConeTotalCoefficient.totalIso (F ⋙ G) U P).hom =
    (G.mapHomologicalComplex (.up ℕ)).map (TotalCoefficient.CechConeTotalCoefficient.totalIso F U P).hom ≫
      (TotalCoefficient.CechConeTotalCoefficient.totalIso G U (TotalCoefficient.CechConeTotalCoefficient.mapped F P)).hom := by
  let K := Total.CechConeTotal.bicomplex U P
  let L := Total.CechConeTotal.bicomplex U (TotalCoefficient.CechConeTotalCoefficient.mapped F P)
  let bF := (TotalCoefficient.CechConeTotalCoefficient.bicomplexIso F U P).hom
  let bG := (TotalCoefficient.CechConeTotalCoefficient.bicomplexIso G U (TotalCoefficient.CechConeTotalCoefficient.mapped F P)).hom
  let GF := G.mapHomologicalComplex (.up ℕ)
  let TT := HomologicalComplex₂.totalFunctor D (.up ℕ) (.up ℕ) (.up ℕ)
  have hBi := (congrArg TT.map (bicomplex F G U P)).trans
    (TT.map_comp (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap G bF) bG)
  have hInv := IntegralComparison.InverseCoordinateHomology.inverse
    (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K))
    (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G L)
    (HomologicalComplex₂.total.map (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap G bF) (.up ℕ))
    (GF.map (HomologicalComplex₂.total.map bF (.up ℕ)))
    (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.natural G bF)
  have hRaw := TotalCoefficient.TotalCoefficientIsoComposition.inv F G K
  exact (congrArg₂ (fun a b => a ≫ b) hRaw hBi).trans
    ((fourFactors _ _ _ _ _ _ hInv.symm).trans
      (congrArg (fun a => a ≫ (TotalCoefficient.CechConeTotalCoefficient.totalIso G U (TotalCoefficient.CechConeTotalCoefficient.mapped F P)).hom)
        (GF.map_comp (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso F K).inv
          (HomologicalComplex₂.total.map bF (.up ℕ))).symm))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.CoefficientComposition.CechConeCoefficientComposition
