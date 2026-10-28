import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DiagramAugmentationProduct

/-! # Diagram Augmentation Graded Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DiagramAugmentationGradedProduct

noncomputable section

/-! The original Čech augmentation from a genuinely multiplicative
complex-valued cone preserves products in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v r t
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  (R : Type r) [CommRing R] {ι : Type} [Finite ι] (U : ι → C)
  (P : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{t} R) ℕ)
  (M : CochainComplex (ModuleCat.{t} R) ℕ) (η : (Functor.const Cᵒᵖ).obj M ⟶ P)
  (μ : ∀ a b (V : Cᵒᵖ), (P.obj V).X a →ₗ[R] (P.obj V).X b →ₗ[R] (P.obj V).X (a + b))
  (σ : ∀ a b, M.X a →ₗ[R] M.X b →ₗ[R] M.X (a + b))
  (hσ : ∀ a b V x y, (η.app V).f (a + b) (σ a b x y) =
    μ a b V ((η.app V).f a x) ((η.app V).f b y))

local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramCoordinates.complex P

private theorem front_zero : AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion 0 0 = 𝟙 ⦋0⦌ := by
  ext i
  simp [AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion]

private theorem back_zero : AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion 0 0 = 𝟙 ⦋0⦌ := by
  ext i
  simp [AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion]

include hσ in
omit [Finite ι] in
theorem restriction_product (a b : ℕ) (x : M.X a) (y : M.X b) :
    DiagramAugmentationCoordinates.Complex.restriction U P M η (a + b) (σ a b x y) =
      Presheaf.CechProduct.cup.{u,v,0,t,r} N Q μ a b 0 0
        (DiagramAugmentationCoordinates.Complex.restriction U P M η a x) (DiagramAugmentationCoordinates.Complex.restriction U P M η b y) := by
  change DiagramAugmentationCoordinates.Complex.restriction U P M η (a + b) (σ a b x y) =
    BilinearPairing.pairing N ((Q).X a) ((Q).X b) ((Q).X (a + b)) (μ a b) ⦋0⦌
      ((BilinearPairing.cosimplicial N ((Q).X a)).map (AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion 0 0)
        (DiagramAugmentationCoordinates.Complex.restriction U P M η a x))
      ((BilinearPairing.cosimplicial N ((Q).X b)).map (AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion 0 0)
        (DiagramAugmentationCoordinates.Complex.restriction U P M η b y))
  erw [front_zero, back_zero, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  change DiagramAugmentationCoordinates.Complex.restriction U P M η (a + b) (σ a b x y) =
    BilinearPairing.pairing N ((Q).X a) ((Q).X b) ((Q).X (a + b)) (μ a b) ⦋0⦌
      (DiagramAugmentationCoordinates.Complex.restriction U P M η a x) (DiagramAugmentationCoordinates.Complex.restriction U P M η b y)
  apply Module.ProductScalarKernel.element_ext
    (fun i => (P.obj (op (((N).obj (op ⦋0⦌)).obj i))).X (a + b))
  intro i
  change BilinearPairing.projection N ((Q).X (a + b)) ⦋0⦌ i _ =
    BilinearPairing.projection N ((Q).X (a + b)) ⦋0⦌ i _
  erw [BilinearPairing.projection_pairing]
  have hr (q : ℕ) (z : M.X q) :
      BilinearPairing.projection N ((Q).X q) ⦋0⦌ i (DiagramAugmentationCoordinates.Complex.restriction U P M η q z) =
        (η.app (op (((N).obj (op ⦋0⦌)).obj i))).f q z :=
    ConcreteCategory.congr_hom (Pi.lift_comp_π (P := M.X q)
      (f := fun j : ((N).obj (op ⦋0⦌)).I => (P.obj (op (((N).obj (op ⦋0⦌)).obj j))).X q)
      (fun j : ((N).obj (op ⦋0⦌)).I => (η.app (op (((N).obj (op ⦋0⦌)).obj j))).f q) i) z
  rw [hr, hr, hr]
  exact hσ a b _ x y

include hσ in
theorem augmentation_product (a b : ℕ) (x : M.X a) (y : M.X b) :
    (ComplexDiagramCoordinates.totalIso U P).hom.f (a + b)
        ((GeometricComparison.CechCone.Total.CechConeTotal.augmentation U P M η).f (a + b) (σ a b x y)) =
      Presheaf.TotalCup.CechProduct.totalCup.{u,v,0,t,r} N Q μ a b
        ((ComplexDiagramCoordinates.totalIso U P).hom.f a ((GeometricComparison.CechCone.Total.CechConeTotal.augmentation U P M η).f a x))
        ((ComplexDiagramCoordinates.totalIso U P).hom.f b ((GeometricComparison.CechCone.Total.CechConeTotal.augmentation U P M η).f b y)) := by
  have ha (q : ℕ) (z : M.X q) := ConcreteCategory.congr_hom (DiagramAugmentationCoordinates.Complex.augmentation_component U P M η q) z
  erw [ha, ha, ha, Presheaf.TotalCup.CechProduct.totalCup_ι]
  simp only [zero_mul, pow_zero, one_smul]
  exact congrArg ((CechCoefficient.Total.bicomplex N Q).ιTotal (.up ℕ) (a + b) 0 (a + b) rfl)
    (restriction_product R U P M η μ σ hσ a b x y)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DiagramAugmentationGradedProduct
