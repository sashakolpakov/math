import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter
import OAI.NumberTheory.PadicHodge.GeometricComparison.SemilinearTensor

/-! # Crystalline Pullback Coordinates -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallinePullbackCoordinates.IntrinsicPadicCrystallineScalarCoordinates

/-! The descended big crystalline module rationalizes to the actual
GeometricComparison crystalline vector space under the original Witt-to-p-adic map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]

local notation "W" => WittVector p (ZMod p)
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))

local instance wittInvPair : RingHomInvPair (WittVector.equiv p).symm.toRingHom (WittVector.equiv p).toRingHom :=
  RingHomInvPair.of_ringEquiv (WittVector.equiv p).symm

local instance wittInvPairSymm : RingHomInvPair (WittVector.equiv p).toRingHom (WittVector.equiv p).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (WittVector.equiv p).symm

def integral (Y : Over (Spec (CommRingCat.of (ZMod p)))) : ModuleCat.{2} ℤ_[p] :=
  (Coefficient.IntrinsicPadicCoefficientDescent.restrict p).obj (ModuleCat.of R
    (IntegralComparison.BigCrystallineCohomology.Cohomology (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
      (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) 1))

def wittEquiv (Y : Over (Spec (CommRingCat.of (ZMod p)))) : integral p Y ≃ₛₗ[(WittVector.equiv p).symm.toRingHom]
    Crystalline.CoefficientAdapter.IntegralH1 p Y where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem scalar (r : ℤ_[p]) : (RingEquiv.refl ℚ_[p]) (algebraMap ℤ_[p] ℚ_[p] r) =
    algebraMap W ℚ_[p] ((WittVector.equiv p).symm r) := by
  change algebraMap ℤ_[p] ℚ_[p] r = algebraMap ℤ_[p] ℚ_[p] ((WittVector.equiv p) ((WittVector.equiv p).symm r))
  rw [RingEquiv.apply_symm_apply]

def rationalEquiv (Y : Over (Spec (CommRingCat.of (ZMod p)))) :
    ℚ_[p] ⊗[ℤ_[p]] integral p Y ≃ₗ[ℚ_[p]] Crystalline.CoefficientAdapter.RationalH1 p Y :=
  SemilinearTensor.SemilinearTensorExtension.equiv (WittVector.equiv p).symm (RingEquiv.refl ℚ_[p]) (scalar p) (wittEquiv p Y)

theorem rationalEquiv_tmul (Y : Over (Spec (CommRingCat.of (ZMod p)))) (a : ℚ_[p]) (x : integral p Y) :
    rationalEquiv p Y (a ⊗ₜ[ℤ_[p]] x) = a ⊗ₜ[W] wittEquiv p Y x := rfl

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallinePullbackCoordinates.IntrinsicPadicCrystallineScalarCoordinates

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallinePullbackCoordinates.IntrinsicPadicCrystallinePullbackCoordinates

/-! Original big crystalline pullback descends to p-adic scalars, and
its rationalization is the original GeometricComparison pullback operator. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]
  {X Y : Over (Spec (CommRingCat.of (ZMod p)))} (g : X ⟶ Y)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))

def integral : IntrinsicPadicCrystallineScalarCoordinates.integral p Y →ₗ[ℤ_[p]]
    IntrinsicPadicCrystallineScalarCoordinates.integral p X :=
  ((Coefficient.IntrinsicPadicCoefficientDescent.restrict p).map (ModuleCat.ofHom
    (IntegralComparison.BigCrystallineCohomology.pullback (p := p)
      (J := Ideal.span {(p : WittVector p (ZMod p))})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
      g.left (by simp only [IntegralComparison.Witt.Crystalline.wittStructureMap, ← Category.assoc, Over.w]) 1))).hom

theorem rational (x : ℚ_[p] ⊗[ℤ_[p]] IntrinsicPadicCrystallineScalarCoordinates.integral p Y) :
    IntrinsicPadicCrystallineScalarCoordinates.rationalEquiv p X ((integral p g).baseChange ℚ_[p] x) =
      Crystalline.CoefficientAdapter.rationalPullback p g (IntrinsicPadicCrystallineScalarCoordinates.rationalEquiv p Y x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallinePullbackCoordinates.IntrinsicPadicCrystallinePullbackCoordinates

end

end OAI
