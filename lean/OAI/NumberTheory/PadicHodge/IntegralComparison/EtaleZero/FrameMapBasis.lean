import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FrameFormBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFormBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FormMap

/-! # Frame Map Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FrameMapBasis

noncomputable section

/-!
# IntegralComparison: the original frame map preserves the native coordinate bases
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData

universe u

variable (p : ℕ) [Fact p.Prime] (k C σ : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [Algebra k C] [LinearOrder σ] [Fintype σ]
  [Algebra (MvPolynomial σ k) C] [IsScalarTower k (MvPolynomial σ k) C]
  [Algebra.Etale (MvPolynomial σ k) C]

local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.LevelFrame.boundedFrame p k C
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f 0
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection F
local notation "τ" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols.frameProjection F
local notation "xF" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroCoordinates.frameCoordinate p k C σ

variable (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) 0)

theorem map_basis (m : ℕ) (s : Set.powersetCard σ m) :
    RelativeFrame.FormMap.map H Q π (F).obj τ U m
      (FrameFormBasis.frameBasis p k C σ m s) =
        BoundedEtale.ZeroFormBasis.basis p k C σ U m s := by
  have h1 : ((τ).app U).ringMap (1 : (F).obj.ring) = (1 : ((H).obj U).ring) :=
    ((τ).app U).ringMap.toRingHom.map_one
  exact (congrArg (RelativeFrame.FormMap.map H Q π (F).obj τ U m)
    (FrameFormBasis.frameBasis_apply p k C σ m s)).trans
      ((RelativeFrame.FormMap.map_symbol H Q π (F).obj τ U m 1
        (fun j => xF (Set.powersetCard.ofFinEmbEquiv.symm s j))).trans
          ((congrArg (fun a => RelativeCrystalline.FormData.symbol H Q π U m a
            (fun j => ((τ).app U).ringMap (xF (Set.powersetCard.ofFinEmbEquiv.symm s j)))) h1).trans
              (BoundedEtale.ZeroFormBasis.basis_apply p k C σ U m s).symm))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FrameMapBasis
