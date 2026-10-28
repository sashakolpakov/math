import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FrameProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols

/-! # Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.Coordinates

noncomputable section

/-! Actual chart coordinates on the native bounded smooth finite-level frame product. -/

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

def frameCoordinate (i : σ) : A :=
  algebraMap (MvPolynomial σ (Truncated.Witt.Ring p k n)) A (MvPolynomial.X i)

variable (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) n)

local notation "β" => CategoryTheory.Functor.map Q
  (FrameProduct.presentationMorphism p k n A C ρ hρ hker hbase U)
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FrameProduct.coordinateIso p k n A C σ ρ hρ hker hbase U
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DividedCoordinates.object U.obj σ

omit [Fintype k] [Fintype σ] in
theorem coordinateIso_frameProjection : (e).hom ≫ (BoundedFrame.Symbols.frameProjection F).app U =
    Truncated.FrameDividedMap.frameMap p k n A C ρ hρ hker hbase U.obj β σ := by
  rw [BoundedFrame.Symbols.frameProjection_app]
  exact (BinaryFan.isLimitFlip (Truncated.FrameProduct.isProduct p k n A C ρ hρ hker hbase U.obj β σ)).conePointUniqueUpToIso_hom_comp
    (FrameProduct.productIsLimit p k n A C ρ hρ hker hbase U) ⟨WalkingPair.left⟩

def coordinate (i : σ) : ((BoundedFrame.Diagram.productDiagram F).obj U).ring :=
  ((BoundedFrame.Symbols.frameProjection F).app U).ringMap (frameCoordinate p k n A σ i)

omit [Fintype k] [Fintype σ] in
theorem coordinate_formula (i : σ) : (e).hom.ringMap (coordinate p k n A C σ ρ hρ hker hbase U i) =
    algebraMap U.obj.ring (G).ring ((β).ringMap (frameCoordinate p k n A σ i)) +
      (show (G).ring from AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator U.obj.ring σ 1 i) := by
  refine (congrArg (fun α : G ⟶ (F).obj => α.ringMap (frameCoordinate p k n A σ i))
    (coordinateIso_frameProjection p k n A C σ ρ hρ hker hbase U)).trans ?_
  let := Truncated.FrameAlgebras.ambientAlgebra p k n A C ρ hρ hker hbase U.obj β
  exact IntegralComparison.Etale.DividedCoordinateLift.lift_coordinate (Truncated.Witt.Ring p k n) σ A U.obj.ring U.obj.ideal p U.obj.dividedPowers
    U.obj.primeNilpotent (Truncated.FrameAlgebras.chartMap p k n A C ρ hρ hker hbase U.obj β) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.Coordinates
