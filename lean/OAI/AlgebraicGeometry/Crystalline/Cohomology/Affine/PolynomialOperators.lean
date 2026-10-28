import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameTower

/-! # Polynomial Operators -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialOperators.AffinePolynomialOperators

noncomputable section

/-! # Coordinate derivatives on the original completed affine envelope -/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k
local notation "Poly" => MvPolynomial σ W
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.frame p k B Poly r hr hbase
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B Poly r hr hbase
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit.PDInverseLimit.Ring p k B Tower
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.derivation p k B σ r hr hbase

def derivative (i : σ) : Module.End W C where
  toFun a := ⟨fun n => D n i (a.val n), by
    intro n m h
    change PolynomialFrameTower.AffinePolynomialFrameTower.transition p k B σ r hr hbase n m h
      (D m i (a.val m)) = D n i (a.val n)
    exact (PolynomialFrameTower.AffinePolynomialFrameTower.derivative_transition p k B σ r hr hbase n m h i
      (a.val m)).symm.trans (congrArg (D n i) (a.property n m h))⟩
  map_add' a b := PD.InverseLimit.PDInverseLimit.ext p k B Tower (fun n => (D n i).map_add (a.val n) (b.val n))
  map_smul' w a := PD.InverseLimit.PDInverseLimit.ext p k B Tower (fun n => (D n i).toLinearMap.map_smul w (a.val n))

theorem eval_derivative (i : σ) (n : ℕ) (a : C) :
    PD.InverseLimit.PDInverseLimit.eval p k B Tower n (derivative p k B σ r hr hbase i a) =
      D n i (PD.InverseLimit.PDInverseLimit.eval p k B Tower n a) := rfl

theorem commute (i j : σ) : Function.Commute
    (derivative p k B σ r hr hbase i) (derivative p k B σ r hr hbase j) := by
  intro a
  apply PD.InverseLimit.PDInverseLimit.ext p k B Tower
  intro n
  rw [eval_derivative, eval_derivative, eval_derivative, eval_derivative]
  exact PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.commute p k B σ r hr hbase n i j _

def complex [Fintype σ] : CochainComplex (ModuleCat.{u} W) ℕ :=
  Koszul.Tensor.KoszulTensor.complex W σ C (derivative p k B σ r hr hbase) (commute p k B σ r hr hbase)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialOperators.AffinePolynomialOperators
