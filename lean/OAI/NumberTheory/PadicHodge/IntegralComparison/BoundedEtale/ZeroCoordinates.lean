import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFrameProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols

/-! # Zero Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroCoordinates

noncomputable section

/-!
# IntegralComparison: étale chart coordinates on the native zero-frame product
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k C σ : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [Algebra k C] [Fintype σ] [Algebra (MvPolynomial σ k) C]
  [IsScalarTower k (MvPolynomial σ k) C] [Algebra.Etale (MvPolynomial σ k) C]

local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.LevelFrame.boundedFrame p k C
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f 0

def frameCoordinate (i : σ) : (F).obj.ring := algebraMap (MvPolynomial σ k) C (MvPolynomial.X i)

variable (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) 0)

local notation "β" => CategoryTheory.Functor.map Q (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFrameProduct.presentationMorphism p k C σ U)
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFrameProduct.coordinateIso p k C σ U
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DividedCoordinates.object U.obj σ

theorem coordinateIso_frameProjection : (e).hom ≫ (BoundedFrame.Symbols.frameProjection F).app U =
    EtaleZero.FrameMap.frameMap p k C σ U.obj β := by
  rw [BoundedFrame.Symbols.frameProjection_app]
  exact (BinaryFan.isLimitFlip (EtaleZero.FrameProduct.isProduct p k C σ U.obj β)).conePointUniqueUpToIso_hom_comp
    (ZeroFrameProduct.productIsLimit p k C U) ⟨WalkingPair.left⟩

def coordinate (i : σ) : ((BoundedFrame.Diagram.productDiagram F).obj U).ring :=
  ((BoundedFrame.Symbols.frameProjection F).app U).ringMap (frameCoordinate p k C σ i)

def generator (i : σ) : (G).ring := AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator U.obj.ring σ 1 i

theorem coordinate_formula (i : σ) : (e).hom.ringMap (coordinate p k C σ U i) =
    algebraMap U.obj.ring (G).ring ((β).ringMap (frameCoordinate p k C σ i)) +
      generator p k C σ U i := by
  refine (congrArg (fun α : G ⟶ (F).obj => α.ringMap (frameCoordinate p k C σ i))
    (coordinateIso_frameProjection p k C σ U)).trans ?_
  let := Zero.FrameAlgebras.ambientAlgebra p k C U.obj β
  exact IntegralComparison.Etale.DividedCoordinateLift.lift_coordinate k σ C U.obj.ring U.obj.ideal p U.obj.dividedPowers
    U.obj.primeNilpotent (Zero.FrameAlgebras.chartMap p k C U.obj β) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroCoordinates
