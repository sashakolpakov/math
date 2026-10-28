import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameFormBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FormBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FormMap

/-! # Frame Map Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameMapBasis

noncomputable section

/-! The original smooth finite-level frame map preserves the native coordinate form bases. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (A C σ : Type) [CommRing A] [CommRing C]
  [Algebra (Witt.Ring p k n) A]
  [Algebra.Smooth (Witt.Ring p k n) A] [Algebra k C]
  [LinearOrder σ] [Fintype σ]
  [Algebra (MvPolynomial σ (Witt.Ring p k n)) A]
  [IsScalarTower (Witt.Ring p k n)
    (MvPolynomial σ (Witt.Ring p k n)) A]
  [Algebra.Etale (MvPolynomial σ (Witt.Ring p k n)) A]
  (ρ : A →+* C) (hρ : Function.Surjective ρ)
  (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k,
    ρ (algebraMap (Witt.Ring p k n) A (Witt.quotient p k n w)) =
      algebraMap k C (WittVector.constantCoeff w))

local notation "W" => WittVector p k
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame.boundedFrame p A C ρ hρ hker k n hbase
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : W)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n

local instance structureMap_separated : IsSeparated f :=
  BoundedTruncated.FrameProduct.structureMap_separated p k C

open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData

local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection F
local notation "τ" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols.frameProjection F
local notation "xF" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.Coordinates.frameCoordinate p k n A σ

variable (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) n)

omit [Fintype k] [Fintype σ] in
theorem map_basis (m : ℕ) (s : Set.powersetCard σ m) :
    RelativeFrame.FormMap.map H Q π (F).obj τ U m
      (FrameFormBasis.frameBasis p k n A σ C ρ hρ hker hbase m s) =
        BoundedTruncated.FormBasis.basis p k n A C σ ρ hρ hker hbase U m s := by
  have h1 : ((τ).app U).ringMap (1 : (F).obj.ring) = (1 : ((H).obj U).ring) :=
    ((τ).app U).ringMap.toRingHom.map_one
  exact (congrArg (RelativeFrame.FormMap.map H Q π (F).obj τ U m)
    (FrameFormBasis.frameBasis_apply p k n A σ C ρ hρ hker hbase m s)).trans
      ((RelativeFrame.FormMap.map_symbol H Q π (F).obj τ U m 1
        (fun j => xF (Set.powersetCard.ofFinEmbEquiv.symm s j))).trans
          ((congrArg (fun a => RelativeCrystalline.FormData.symbol H Q π U m a
            (fun j => ((τ).app U).ringMap (xF (Set.powersetCard.ofFinEmbEquiv.symm s j)))) h1).trans
              (BoundedTruncated.FormBasis.basis_apply p k n A C σ ρ hρ hker hbase U m s).symm))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameMapBasis
