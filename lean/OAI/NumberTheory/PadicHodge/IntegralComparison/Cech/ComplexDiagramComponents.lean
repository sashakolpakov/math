import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramCoordinates

/-! # Complex Diagram Components -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramComponents.Coordinates

noncomputable section

/-! Component formulas for the actual Čech diagram coordinate
isomorphism, retaining canonical product projections and total inclusions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v w z
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {ι : Type} [Finite ι] (U : ι → C) (P : Cᵒᵖ ⥤ CochainComplex A ℕ)

local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Total.CechConeTotal.bicomplex U P
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Total.bicomplex N (OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramCoordinates.complex P)

omit [HasCoproducts A] in
theorem row_projection (a b : ℕ) (i : ((N).obj (op ⦋b⦌)).I) :
    (ComplexDiagramCoordinates.rowIso U P a).hom.f b ≫
        Pi.π (fun j => (P.obj (op (((N).obj (op ⦋b⦌)).obj j))).X a) i =
      (Pi.π (fun j => P.obj (op (((N).obj (op ⦋b⦌)).obj j))) i).f a := by
  rw [ComplexDiagramCoordinates.rowIso, GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.hom_f]
  exact piComparison_comp_π (HomologicalComplex.eval A (.up ℕ) a)
    (fun j => P.obj (op (((N).obj (op ⦋b⦌)).obj j))) i

theorem component (a b n : ℕ) (h : a + b = n) :
    (K).ιTotal (.up ℕ) a b n h ≫ (ComplexDiagramCoordinates.totalIso U P).hom.f n =
      (ComplexDiagramCoordinates.rowIso U P a).hom.f b ≫ (L).ιTotal (.up ℕ) a b n h :=
  HomologicalComplex₂.ιTotal_map K L (ComplexDiagramCoordinates.bicomplexIso U P).hom (.up ℕ) a b n h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramComponents.Coordinates
