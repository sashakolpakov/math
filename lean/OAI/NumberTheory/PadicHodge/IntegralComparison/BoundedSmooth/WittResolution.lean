import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFrameProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModulePoincare
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex

/-! # Witt Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittResolution

noncomputable section

/-! The smooth Witt frame resolves the actual original bounded crystalline structure sheaf. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k A C σ : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C] [Fintype σ]
  [Algebra (MvPolynomial σ (WittVector p k)) A]
  [IsScalarTower (WittVector p k) (MvPolynomial σ (WittVector p k)) A]
  [Algebra.Etale (MvPolynomial σ (WittVector p k)) A]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w)) (n : ℕ)

local notation "W" => WittVector p k
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame.boundedFrame p k A C ρ hρ hker hbase n
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : W)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n

local instance structureMap_separated : IsSeparated f :=
  WittFrameProduct.structureMap_separated p k C

include σ in
theorem presheaf_augmentation_quasiIso : QuasiIso (BoundedFrame.Diagram.augmentation F) :=
  RelativeCrystalline.ModulePoincare.augmentation_quasiIso
    (BoundedFrame.Diagram.productDiagram F) BoundedFrame.Diagram.baseDiagram
    (BoundedFrame.Diagram.projection F) σ (fun U =>
      ⟨WittFrameProduct.coordinateIso p k A C σ ρ hρ hker hbase n U,
        WittFrameProduct.coordinateIso_projection p k A C σ ρ hρ hker hbase n U⟩)

include σ in
theorem augmentation_quasiIso : QuasiIso (Bounded.RelativeSheafComplex.augmentation f n F) := by
  let : QuasiIso (BoundedFrame.Diagram.augmentation F) :=
    presheaf_augmentation_quasiIso p k A C σ ρ hρ hker hbase n
  exact Bounded.RelativeSheafComplex.augmentation_quasiIso f n F

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittResolution
