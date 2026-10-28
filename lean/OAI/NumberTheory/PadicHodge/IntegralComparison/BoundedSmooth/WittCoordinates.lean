import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFrameProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols

/-! # Witt Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittCoordinates

noncomputable section

/-! Actual chart coordinates on the native bounded smooth Witt frame product. -/

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

def frameCoordinate (i : σ) : SmoothWitt.FrameRing.Ring p A n :=
  Ideal.Quotient.mk ((Ideal.span {(p : A)}) ^ (n + 1))
    (algebraMap (MvPolynomial σ W) A (MvPolynomial.X i))

variable (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) n)

local notation "β" => CategoryTheory.Functor.map Q
  (WittFrameProduct.presentationMorphism p k A C σ ρ hρ hker hbase n U)
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFrameProduct.coordinateIso p k A C σ ρ hρ hker hbase n U
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DividedCoordinates.object U.obj σ

theorem coordinateIso_frameProjection : (e).hom ≫ (BoundedFrame.Symbols.frameProjection F).app U =
    SmoothWitt.FrameDividedMap.frameMap p k A C ρ hρ hker hbase n U.obj β σ := by
  rw [BoundedFrame.Symbols.frameProjection_app]
  exact (BinaryFan.isLimitFlip (SmoothWitt.FrameProduct.isProduct p k A C ρ hρ hker hbase n U.obj β σ)).conePointUniqueUpToIso_hom_comp
    (WittFrameProduct.productIsLimit p k A C ρ hρ hker hbase n U) ⟨WalkingPair.left⟩

def coordinate (i : σ) : ((BoundedFrame.Diagram.productDiagram F).obj U).ring :=
  ((BoundedFrame.Symbols.frameProjection F).app U).ringMap (frameCoordinate p k A σ n i)

theorem coordinate_formula (i : σ) : (e).hom.ringMap (coordinate p k A C σ ρ hρ hker hbase n U i) =
    algebraMap U.obj.ring (G).ring ((β).ringMap (frameCoordinate p k A σ n i)) +
      (show (G).ring from AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator U.obj.ring σ 1 i) := by
  refine (congrArg (fun α : G ⟶ (F).obj => α.ringMap (frameCoordinate p k A σ n i))
    (coordinateIso_frameProjection p k A C σ ρ hρ hker hbase n U)).trans ?_
  let := SmoothWitt.FrameLifting.ambientAlgebra p k C U.obj
  exact IntegralComparison.Etale.DividedCoordinateLift.lift_coordinate W σ A U.obj.ring U.obj.ideal p U.obj.dividedPowers
    U.obj.primeNilpotent (SmoothWitt.FrameAlgebras.chartMap p k A C ρ hρ hker hbase n U.obj β) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittCoordinates
