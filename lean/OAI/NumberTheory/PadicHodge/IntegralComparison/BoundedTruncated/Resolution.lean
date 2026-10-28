import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FrameProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModulePoincare
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex

/-! # Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.Resolution

noncomputable section

/-! The smooth finite-level frame resolves the actual original bounded crystalline structure sheaf. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (A C σ : Type) [CommRing A] [CommRing C]
  [Algebra (Truncated.Witt.Ring p k n) A]
  [Algebra.Smooth (Truncated.Witt.Ring p k n) A] [Algebra k C]
  [Fintype σ]
  [Algebra (MvPolynomial σ (Truncated.Witt.Ring p k n)) A]
  [IsScalarTower (Truncated.Witt.Ring p k n)
    (MvPolynomial σ (Truncated.Witt.Ring p k n)) A]
  [Algebra.Etale (MvPolynomial σ (Truncated.Witt.Ring p k n)) A]
  (ρ : A →+* C) (hρ : Function.Surjective ρ)
  (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k,
    ρ (algebraMap (Truncated.Witt.Ring p k n) A (Truncated.Witt.quotient p k n w)) =
      algebraMap k C (WittVector.constantCoeff w))

local notation "W" => WittVector p k
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame.boundedFrame p A C ρ hρ hker k n hbase
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : W)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n

local instance structureMap_separated : IsSeparated f :=
  FrameProduct.structureMap_separated p k C

include σ in
omit [Fintype k] in
theorem presheaf_augmentation_quasiIso : QuasiIso (BoundedFrame.Diagram.augmentation F) :=
  RelativeCrystalline.ModulePoincare.augmentation_quasiIso
    (BoundedFrame.Diagram.productDiagram F) BoundedFrame.Diagram.baseDiagram
    (BoundedFrame.Diagram.projection F) σ (fun U =>
      ⟨FrameProduct.coordinateIso p k n A C σ ρ hρ hker hbase U,
        FrameProduct.coordinateIso_projection p k n A C σ ρ hρ hker hbase U⟩)

include σ in
omit [Fintype k] in
theorem augmentation_quasiIso : QuasiIso (Bounded.RelativeSheafComplex.augmentation f n F) := by
  let : QuasiIso (BoundedFrame.Diagram.augmentation F) :=
    presheaf_augmentation_quasiIso p k n A C σ ρ hρ hker hbase
  exact Bounded.RelativeSheafComplex.augmentation_quasiIso f n F

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.Resolution
