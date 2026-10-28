import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DiagramAugmentationCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.TotalCup

/-! # Diagram Augmentation Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DiagramAugmentationProduct

noncomputable section

/-! A multiplicative local augmentation remains multiplicative in
its literal degree-zero global Čech total augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DiagramAugmentationCoordinates.Complex
universe u v r t
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  (R : Type r) [CommRing R] {ι : Type} [Finite ι] (U : ι → C)
  (P : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{t} R) ℕ)
  (M : CochainComplex (ModuleCat.{t} R) ℕ) (η : (Functor.const Cᵒᵖ).obj M ⟶ P)
  (μ : ∀ a b (V : Cᵒᵖ), (P.obj V).X a →ₗ[R] (P.obj V).X b →ₗ[R] (P.obj V).X (a + b))
  (σ : M.X 0 →ₗ[R] M.X 0 →ₗ[R] M.X 0)
  (hσ : ∀ V x y, (η.app V).f 0 (σ x y) = μ 0 0 V ((η.app V).f 0 x) ((η.app V).f 0 y))

local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramCoordinates.complex P
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.TotalCup.CechProduct.total N Q

private theorem front_zero : AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion 0 0 = 𝟙 ⦋0⦌ := by
  ext i
  simp [AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion]

private theorem back_zero : AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion 0 0 = 𝟙 ⦋0⦌ := by
  ext i
  simp [AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion]

include hσ in
omit [Finite ι] in
theorem restriction_product (x y : M.X 0) :
    DiagramAugmentationCoordinates.Complex.restriction U P M η 0 (σ x y) =
      Presheaf.CechProduct.cup.{u,v,0,t,r} N Q μ 0 0 0 0
        (DiagramAugmentationCoordinates.Complex.restriction U P M η 0 x) (DiagramAugmentationCoordinates.Complex.restriction U P M η 0 y) := by
  change DiagramAugmentationCoordinates.Complex.restriction U P M η 0 (σ x y) =
    BilinearPairing.pairing N ((Q).X 0) ((Q).X 0) ((Q).X 0) (μ 0 0) ⦋0⦌
      ((BilinearPairing.cosimplicial N ((Q).X 0)).map (AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion 0 0)
        (DiagramAugmentationCoordinates.Complex.restriction U P M η 0 x))
      ((BilinearPairing.cosimplicial N ((Q).X 0)).map (AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion 0 0)
        (DiagramAugmentationCoordinates.Complex.restriction U P M η 0 y))
  erw [front_zero, back_zero, CategoryTheory.Functor.map_id]
  change DiagramAugmentationCoordinates.Complex.restriction U P M η 0 (σ x y) =
    BilinearPairing.pairing N ((Q).X 0) ((Q).X 0) ((Q).X 0) (μ 0 0) ⦋0⦌
      (DiagramAugmentationCoordinates.Complex.restriction U P M η 0 x) (DiagramAugmentationCoordinates.Complex.restriction U P M η 0 y)
  apply Module.ProductScalarKernel.element_ext
    (fun i => (P.obj (op (((N).obj (op ⦋0⦌)).obj i))).X 0)
  intro i
  change BilinearPairing.projection N ((Q).X 0) ⦋0⦌ i _ =
    BilinearPairing.projection N ((Q).X 0) ⦋0⦌ i _
  erw [BilinearPairing.projection_pairing]
  have hr (z : M.X 0) :
      BilinearPairing.projection N ((Q).X 0) ⦋0⦌ i (DiagramAugmentationCoordinates.Complex.restriction U P M η 0 z) =
        (η.app (op (((N).obj (op ⦋0⦌)).obj i))).f 0 z :=
    ConcreteCategory.congr_hom (Pi.lift_comp_π (P := M.X 0)
      (f := fun j : ((N).obj (op ⦋0⦌)).I => (P.obj (op (((N).obj (op ⦋0⦌)).obj j))).X 0)
      (fun j : ((N).obj (op ⦋0⦌)).I => (η.app (op (((N).obj (op ⦋0⦌)).obj j))).f 0) i) z
  rw [hr, hr, hr]
  exact hσ _ x y

include hσ in
theorem augmentation_product (x y : M.X 0) :
    (ComplexDiagramCoordinates.totalIso U P).hom.f 0 ((GeometricComparison.CechCone.Total.CechConeTotal.augmentation U P M η).f 0 (σ x y)) =
      Presheaf.TotalCup.CechProduct.totalCup.{u,v,0,t,r} N Q μ 0 0
        ((ComplexDiagramCoordinates.totalIso U P).hom.f 0 ((GeometricComparison.CechCone.Total.CechConeTotal.augmentation U P M η).f 0 x))
        ((ComplexDiagramCoordinates.totalIso U P).hom.f 0 ((GeometricComparison.CechCone.Total.CechConeTotal.augmentation U P M η).f 0 y)) := by
  have ha (z : M.X 0) := ConcreteCategory.congr_hom (DiagramAugmentationCoordinates.Complex.augmentation_component U P M η 0) z
  erw [ha, ha, ha]
  erw [Presheaf.TotalCup.CechProduct.totalCup_ι]
  simp only [zero_mul, pow_zero, one_smul]
  exact congrArg ((CechCoefficient.Total.bicomplex N Q).ιTotal (.up ℕ) 0 0 0 rfl)
    (restriction_product R U P M η μ σ hσ x y)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DiagramAugmentationProduct
