import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramComponents

/-! # Diagram Augmentation Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DiagramAugmentationCoordinates.Complex

noncomputable section

/-! The native diagram Čech augmentation becomes the literal family
of its local augmentation components in degreewise total coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial

open _root_.Complex

universe u v w z
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {ι : Type} [Finite ι] (U : ι → C) (P : Cᵒᵖ ⥤ CochainComplex A ℕ)
  (M : CochainComplex A ℕ) (η : (Functor.const Cᵒᵖ).obj M ⟶ P)

local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Total.bicomplex N (OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramCoordinates.complex P)

def restriction (q : ℕ) : M.X q ⟶ ((L).X q).X 0 :=
  Pi.lift (fun i => (η.app (op (((N).obj (op ⦋0⦌)).obj i))).f q)

omit [HasCoproducts A] in
theorem component_restriction (q : ℕ) :
    GeometricComparison.CechCone.Total.CechConeTotal.component U P M η q ≫ (ComplexDiagramCoordinates.rowIso U P q).hom.f 0 =
      restriction U P M η q := by
  apply Pi.hom_ext
  intro i
  erw [Category.assoc, ComplexDiagramComponents.Coordinates.row_projection, restriction, Pi.lift_comp_π]
  exact congrArg (fun a : M ⟶ P.obj (op (((N).obj (op ⦋0⦌)).obj i)) => a.f q)
    (Pi.lift_comp_π (fun j => η.app (op (((N).obj (op ⦋0⦌)).obj j))) i)

theorem augmentation_component (q : ℕ) :
    (GeometricComparison.CechCone.Total.CechConeTotal.augmentation U P M η).f q ≫ (ComplexDiagramCoordinates.totalIso U P).hom.f q =
      restriction U P M η q ≫ (L).ιTotal (.up ℕ) q 0 q rfl := by
  change (GeometricComparison.CechCone.Total.CechConeTotal.component U P M η q ≫
    (GeometricComparison.CechCone.Total.CechConeTotal.bicomplex U P).ιTotal (.up ℕ) q 0 q rfl) ≫
    (ComplexDiagramCoordinates.totalIso U P).hom.f q = _
  erw [Category.assoc, ComplexDiagramComponents.Coordinates.component, ← Category.assoc, component_restriction]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DiagramAugmentationCoordinates.Complex
