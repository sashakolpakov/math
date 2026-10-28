import OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.RowCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CechCoefficientChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Total

/-! # Double Cech Regrouping -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DoubleCechRegrouping

noncomputable section

/-! The genuine triple total maps to the original Čech total of the
row totals. The coordinate map uses the finite Čech coefficient
comparison and preserves the existing differential conventions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w z
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {ι : Type} [Finite ι] (U : ι → C)
  (P : Cᵒᵖ ⥤ HomologicalComplex₂ A (.up ℕ) (.up ℕ))
attribute [local instance] TripleTotal.Rotation.total TripleTotal.Rotation.complexTotal

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.RowCoordinates.rowFunctor (A := A)
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U

def triple : HomologicalComplex₂ (CochainComplex A ℕ) (.up ℕ) (.up ℕ) :=
  HomologicalComplex₂.flip ((NonemptyCechNerve.complexFunctor U).obj P)

def coordinateIso : TripleTotal.RowCoordinates.bicomplex (triple U P) ≅
    GeometricComparison.CechCone.Total.CechConeTotal.bicomplex U (P ⋙ F) :=
  (HomologicalComplex₂.flipFunctor A (.up ℕ) (.up ℕ)).mapIso
    (GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.complexIso F N
      (fun _ => inferInstanceAs (Finite (Fin _ → ι))) P)

def totalIso : (TripleTotal.RowCoordinates.bicomplex (triple U P)).total (.up ℕ) ≅
    GeometricComparison.CechCone.Total.CechConeTotal.total U (P ⋙ F) :=
  HomologicalComplex₂.total.mapIso (coordinateIso U P) (.up ℕ)

def map : (HomologicalComplex₂.flip ((triple U P).total (.up ℕ))).total (.up ℕ) ⟶
    GeometricComparison.CechCone.Total.CechConeTotal.total U (P ⋙ F) :=
  TripleTotal.RowCoordinates.regroup (triple U P) ≫ (totalIso U P).hom

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DoubleCechRegrouping
