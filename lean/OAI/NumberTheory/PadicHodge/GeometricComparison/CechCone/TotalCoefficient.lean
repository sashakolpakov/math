import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Total
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CechCoefficientChange
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Total Coefficient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient

noncomputable section

/-! Finite actual Čech totals of complex-valued coefficients commute with
additive functors, including slice restriction and sheafification. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v w z w' z' t
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{t} A] [HasCoproducts.{0} A]
  {B : Type w'} [Category.{z'} B] [Abelian B] [HasProducts.{t} B] [HasCoproducts.{0} B]
  (F : A ⥤ B) [F.Additive] {ι : Type t} [Finite ι] (U : ι → C)
  (P : Cᵒᵖ ⥤ CochainComplex A ℕ)

local instance finiteBiproducts : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts

def mapped : Cᵒᵖ ⥤ CochainComplex B ℕ := P ⋙ F.mapHomologicalComplex (.up ℕ)

theorem finite_indices (n : SimplexCategory) : Finite ((IntegralComparison.NonemptyCechNerve.nerve U).obj (op n)).I :=
  inferInstanceAs (Finite (Fin (n.len + 1) → ι))

def horizontalIso : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F (Total.CechConeTotal.horizontal U P) ≅
    Total.CechConeTotal.horizontal U (mapped F P) :=
  GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.complexIso (F.mapHomologicalComplex (.up ℕ))
    (IntegralComparison.NonemptyCechNerve.nerve U) (finite_indices U) P

def bicomplexIso : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F (Total.CechConeTotal.bicomplex U P) ≅
    Total.CechConeTotal.bicomplex U (mapped F P) :=
  (HomologicalComplex₂.flipFunctor B (.up ℕ) (.up ℕ)).mapIso (horizontalIso F U P)

def totalIso : (F.mapHomologicalComplex (.up ℕ)).obj (Total.CechConeTotal.total U P) ≅
    Total.CechConeTotal.total U (mapped F P) :=
  (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso F (Total.CechConeTotal.bicomplex U P)).symm ≪≫
    HomologicalComplex₂.total.mapIso (bicomplexIso F U P) (.up ℕ)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient
