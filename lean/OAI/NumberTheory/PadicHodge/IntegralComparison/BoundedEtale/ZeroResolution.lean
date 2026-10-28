import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFrameProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModulePoincare
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex

/-! # Zero Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroResolution

noncomputable section

/-!
# IntegralComparison: the original étale zero frame resolves the restricted crystalline structure sheaf
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k C σ : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [Algebra k C] [Fintype σ] [Algebra (MvPolynomial σ k) C]
  [IsScalarTower k (MvPolynomial σ k) C] [Algebra.Etale (MvPolynomial σ k) C]

local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.LevelFrame.boundedFrame p k C

include σ in
theorem presheaf_augmentation_quasiIso : QuasiIso (BoundedFrame.Diagram.augmentation F) :=
  RelativeCrystalline.ModulePoincare.augmentation_quasiIso
    (BoundedFrame.Diagram.productDiagram F) BoundedFrame.Diagram.baseDiagram
    (BoundedFrame.Diagram.projection F) σ (fun U =>
      ⟨ZeroFrameProduct.coordinateIso p k C σ U,
        ZeroFrameProduct.coordinateIso_projection p k C σ U⟩)

include σ in
/-- The resolution uses the actual restricted original structure sheaf and its native coefficients. -/
theorem augmentation_quasiIso : QuasiIso (Bounded.RelativeSheafComplex.augmentation f 0 F) := by
  let : QuasiIso (BoundedFrame.Diagram.augmentation F) := presheaf_augmentation_quasiIso p k C σ
  exact Bounded.RelativeSheafComplex.augmentation_quasiIso f 0 F

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroResolution
