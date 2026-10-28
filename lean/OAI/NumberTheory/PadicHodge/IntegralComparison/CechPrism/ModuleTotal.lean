import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.AugmentationHomotopy
import OAI.NumberTheory.PadicHodge.IntegralComparison.FlippedTotalHomotopy

/-! # Module Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.ModuleTotal

noncomputable section

/-! The actual augmentation homotopy remains an equality on total
cohomology when the coefficients are complexes. The original signed
totalization puts the coefficient degree first. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u r v
variable {C : Type u} [SemilatticeInf C]
  (R : Type r) [CommRing R] {ι : Type} [Finite ι] (U : ι → C)
  (Q : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{v} R) ℕ)
  (B : Cᵒᵖ ⥤ Cᵒᵖ ⥤ CochainComplex (ModuleCat.{v} R) ℕ)
  (γ : (Functor.const Cᵒᵖ).obj Q ⟶ B)
  (h : ∀ I V : C, IsIso ((B.obj (op V)).map
    (homOfLE (inf_le_left : I ⊓ V ≤ I)).op))

local instance total (K : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ)) :
    K.HasTotal (.up ℕ) := AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K

def diagonal := HomologicalComplex₂.total.map (GeometricComparison.TotalFlip.TotalFlipNaturality.flipped
  (DiagonalAugmentation.map U Q B γ h)) (.up ℕ)

def global := HomologicalComplex₂.total.map (GeometricComparison.TotalFlip.TotalFlipNaturality.flipped
  (GlobalAugmentation.map U Q B γ)) (.up ℕ)

theorem homology (i : ℕ) : HomologicalComplex.homologyMap (diagonal R U Q B γ h) i =
    HomologicalComplex.homologyMap (global R U Q B γ) i :=
  FlippedTotalHomotopy.homology (AugmentationHomotopy.homotopy U Q B γ h) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.ModuleTotal
