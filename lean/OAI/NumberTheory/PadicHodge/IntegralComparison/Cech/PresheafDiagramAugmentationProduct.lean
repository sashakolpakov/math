import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafDiagramProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DiagramAugmentationProduct
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalAugmentationNaturality

/-! # Presheaf Diagram Augmentation Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafDiagramAugmentationProduct

noncomputable section

/-! The actual presheaf-valued Čech augmentation preserves the native
product whenever its genuine local cone components do. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DiagramSectionCoordinates
universe u v d e r t
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type d} [Category.{e} D] (R : Type r) [CommRing R]
  {ι : Type} [Finite ι] (U : ι → C)
  (P : Cᵒᵖ ⥤ CochainComplex (Dᵒᵖ ⥤ ModuleCat.{t} R) ℕ)
  (M : CochainComplex (Dᵒᵖ ⥤ ModuleCat.{t} R) ℕ)
  (η : (Functor.const Cᵒᵖ).obj M ⟶ P)

local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Total.CechConeTotal.total U P
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Total.CechConeTotal.augmentation U P M η

def mappedSource (T : Dᵒᵖ) := ((DiagramSectionCoordinates.evaluation R T).mapHomologicalComplex (.up ℕ)).obj M

def mappedCone (T : Dᵒᵖ) :=
  GeometricComparison.CechCone.TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone (DiagramSectionCoordinates.evaluation R T) P M η

theorem coordinates (T : Dᵒᵖ) (x : (M.X 0).obj T) :
    (DiagramSectionCoordinates.totalIso R U P T).hom.f 0 (((a).f 0).app T x) =
      (ComplexDiagramCoordinates.totalIso U (DiagramSectionCoordinates.diagram R P T)).hom.f 0
        ((GeometricComparison.CechCone.Total.CechConeTotal.augmentation U (DiagramSectionCoordinates.diagram R P T) (mappedSource R M T)
          (mappedCone R P M η T)).f 0 x) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun b => b.f 0)
      (GeometricComparison.CechCone.TotalAugmentationNaturality.CechConeTotalAugmentationNaturality.augmentation (DiagramSectionCoordinates.evaluation R T) U P M η)) x
  exact congrArg (fun z => (ComplexDiagramCoordinates.totalIso U (DiagramSectionCoordinates.diagram R P T)).hom.f 0 z) h

variable (μ : ∀ n m (V : Cᵒᵖ) (T : Dᵒᵖ), ((P.obj V).X n).obj T →ₗ[R]
  ((P.obj V).X m).obj T →ₗ[R] ((P.obj V).X (n + m)).obj T)
  (σ : ∀ T : Dᵒᵖ, (M.X 0).obj T →ₗ[R] (M.X 0).obj T →ₗ[R] (M.X 0).obj T)
  (hσ : ∀ V T x y, ((η.app V).f 0).app T (σ T x y) =
    μ 0 0 V T (((η.app V).f 0).app T x) (((η.app V).f 0).app T y))

include hσ in
theorem augmentation_product (T : Dᵒᵖ) (x y : (M.X 0).obj T) :
    ((a).f 0).app T (σ T x y) =
      PresheafDiagramProduct.pairing R U P μ 0 0 T
        (((a).f 0).app T x) (((a).f 0).app T y) := by
  apply ((HomologicalComplex.eval _ _ 0).mapIso (DiagramSectionCoordinates.totalIso R U P T)).toLinearEquiv.injective
  change (DiagramSectionCoordinates.totalIso R U P T).hom.f 0 _ = (DiagramSectionCoordinates.totalIso R U P T).hom.f 0 _
  have hp := DiagramAugmentationProduct.augmentation_product R U (DiagramSectionCoordinates.diagram R P T)
    (mappedSource R M T) (mappedCone R P M η T) (fun n m V => μ n m V T) (σ T)
    (fun V x y => hσ V T x y) x y
  exact (coordinates R U P M η T (σ T x y)).trans
    (hp.trans ((congrArg₂
      (fun x y => PresheafDiagramProduct.nativeCup R U P μ T 0 0 x y)
      (coordinates R U P M η T x).symm (coordinates R U P M η T y).symm).trans
      (Cochain.PairingTransport.hom_cup (DiagramSectionCoordinates.totalIso R U P T)
        (PresheafDiagramProduct.nativeCup R U P μ T) 0 0
        (((a).f 0).app T x) (((a).f 0).app T y)).symm))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafDiagramAugmentationProduct
