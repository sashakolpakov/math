import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameFormBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFormBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FormMap

/-! # Frame Map Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameMapBasis

noncomputable section

/-! The original smooth Witt frame map preserves the native coordinate form bases. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k A C σ : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C] [LinearOrder σ] [Fintype σ]
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
  BoundedSmooth.WittFrameProduct.structureMap_separated p k C

open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData

local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection F
local notation "τ" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols.frameProjection F
local notation "xF" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittCoordinates.frameCoordinate p k A σ n

variable (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) n)

theorem map_basis (m : ℕ) (s : Set.powersetCard σ m) :
    RelativeFrame.FormMap.map H Q π (F).obj τ U m
      (FrameFormBasis.frameBasis p k A σ n C ρ hρ hker hbase m s) =
        BoundedSmooth.WittFormBasis.basis p k A C σ ρ hρ hker hbase n U m s := by
  have h1 : ((τ).app U).ringMap (1 : (F).obj.ring) = (1 : ((H).obj U).ring) :=
    ((τ).app U).ringMap.toRingHom.map_one
  exact (congrArg (RelativeFrame.FormMap.map H Q π (F).obj τ U m)
    (FrameFormBasis.frameBasis_apply p k A σ n C ρ hρ hker hbase m s)).trans
      ((RelativeFrame.FormMap.map_symbol H Q π (F).obj τ U m 1
        (fun j => xF (Set.powersetCard.ofFinEmbEquiv.symm s j))).trans
          ((congrArg (fun a => RelativeCrystalline.FormData.symbol H Q π U m a
            (fun j => ((τ).app U).ringMap (xF (Set.powersetCard.ofFinEmbEquiv.symm s j)))) h1).trans
              (BoundedSmooth.WittFormBasis.basis_apply p k A C σ ρ hρ hker hbase n U m s).symm))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameMapBasis
