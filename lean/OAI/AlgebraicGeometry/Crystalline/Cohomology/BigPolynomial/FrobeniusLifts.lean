import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusMorphism
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistPullbackLifts
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PowerCoordinates

/-! # Frobenius Lifts -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusLifts.BigPolynomialFrobeniusLifts

noncomputable section

/-! # Actual chosen frame coordinates under polynomial Frobenius and base twist -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]
  {τ : Type u} (a : τ → MvPolynomial σ k)

local notation "W" => WittVector p k
local notation "B" => MvPolynomial σ k
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)
local notation "φ" => OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.powerRingHom p (Fact.out : p.Prime) B
  (BigCrystalline.AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.prime_zero p k B)
local notation "g" => Spec.map (CommRingCat.ofHom φ)
local notation "e" => WittVector.frobeniusEquiv p k
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W B I γ bX

theorem lift (Q : C) (i : τ) :
    BigCrystalline.FrameLifts.BigCrystallineFrameLifts.lift p W B τ I γ bX a ((FrobeniusMorphism.BigPolynomialFrobeniusMorphism.transformed p k σ).obj Q) i =
      BigCrystalline.FrameLifts.BigCrystallineFrameLifts.lift p W B τ I γ bX (fun j => a j ^ p) Q i :=
  BigCrystalline.TwistPullbackLifts.BigCrystallineTwistPullbackLifts.lift p W B τ I γ bX e
    (NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittFrobeniusDP p k).isDPMorphism φ
    (BigCrystalline.AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.over_base p k B) a Q i

theorem coordinate (Q : C) (i : τ) :
    (show DividedPowerAlgebra Q.ring (τ →₀ Q.ring) from
      BigCrystalline.FrameMaps.BigCrystallineFrameMaps.coordinate a ((FrobeniusMorphism.BigPolynomialFrobeniusMorphism.transformed p k σ).obj Q) i) =
    BigCrystalline.FrameMaps.BigCrystallineFrameMaps.coordinate (fun j => a j ^ p) Q i :=
  BigCrystalline.TwistPullbackLifts.BigCrystallineTwistPullbackLifts.coordinate p W B τ I γ bX e
    (NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittFrobeniusDP p k).isDPMorphism φ
    (BigCrystalline.AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.over_base p k B) a Q i

theorem power_coordinate (Q : C) (i : τ) :
    BigCrystalline.PowerCoordinates.BigCrystallinePowerCoordinates.map a p Q
      (BigCrystalline.FrameMaps.BigCrystallineFrameMaps.coordinate a ((FrobeniusMorphism.BigPolynomialFrobeniusMorphism.transformed p k σ).obj Q) i) =
    BigCrystalline.FrameMaps.BigCrystallineFrameMaps.coordinate a Q i ^ p :=
  (congrArg (BigCrystalline.PowerCoordinates.BigCrystallinePowerCoordinates.map a p Q) (coordinate p k σ a Q i)).trans
    (BigCrystalline.PowerCoordinates.BigCrystallinePowerCoordinates.map_total a p Q i)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusLifts.BigPolynomialFrobeniusLifts
