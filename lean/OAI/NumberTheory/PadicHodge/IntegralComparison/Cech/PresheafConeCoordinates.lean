import Mathlib.Algebra.Homology.Functor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DiagramAugmentationCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeTotal

/-! # Presheaf Cone Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafConeCoordinates

noncomputable section

/-! The two original presentations of a presheaf Čech cone have
canonically identical augmentations after their genuine total coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {ι : Type} [Finite ι] (U : ι → C)
  (K : CochainComplex (Cᵒᵖ ⥤ A) ℕ)

local notation "D" => HomologicalComplex.complexOfFunctorsToFunctorToComplex

def totalIso : GeometricComparison.CechCone.Total.CechConeTotal.total U ((D).obj K) ≅
    (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U K).total (.up ℕ) :=
  ComplexDiagramCoordinates.totalIso U ((D).obj K)

variable (M : CochainComplex A ℕ)
  (η : ((Functor.const Cᵒᵖ).mapHomologicalComplex (.up ℕ)).obj M ⟶ K)

def cone : (Functor.const Cᵒᵖ).obj M ⟶ (D).obj K := (D).map η

theorem augmentation : GeometricComparison.CechCone.Total.CechConeTotal.augmentation U ((D).obj K) M (cone K M η) ≫
    (totalIso U K).hom = GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map U K M η := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact DiagramAugmentationCoordinates.Complex.augmentation_component U ((D).obj K) M
    (cone K M η) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafConeCoordinates
