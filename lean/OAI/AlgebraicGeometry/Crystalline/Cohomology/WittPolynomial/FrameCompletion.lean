import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PadicFrame
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialOperators

/-! # Frame Completion -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.FrameCompletion.WittPolynomialFrameCompletion

noncomputable section

/-! # The completed polynomial coefficients and the original crystalline frame coefficients -/

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "P" => MvPolynomial σ W
local notation "B" => MvPolynomial σ k
local notation "I" => Ideal.span {(p : W)}
local notation "δ₀" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.reduction p k σ
local notation "hr" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_surjective p k σ
local notation "hb" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_base p k σ
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope W P I δ₀ (RingHom.ker r)
local notation "rE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.EnvelopeThickeningP.EnvelopeThickening.envelopeReduction p k B P r hr hb
local notation "δE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.envelopeDP p k B P r hr hb
local notation "hδE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.envelope_baseDP p k B P r hr hb
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B P r hr hb
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit.PDInverseLimit.Ring p k B Tower
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.source p k B σ r hb
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialOperators.AffinePolynomialOperators.derivative p k B σ r hr hb

local instance envelopeBaseAlgebra : Algebra W E :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra W P I δ₀ (RingHom.ker r)).comp (algebraMap W P)).toAlgebra

local instance envelopeScalarTower : IsScalarTower W P E :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

def envelopeLinearEquiv : P ≃ₗ[W] E :=
  (Residue.WittPolynomialResidue.envelopeEquiv p k σ).symm.toLinearEquiv.restrictScalars W

theorem envelopeLinearEquiv_apply (a : P) :
    envelopeLinearEquiv p k σ a = PD.EnvelopeDp.PDEnvelope.ofAlgebra W P I δ₀ (RingHom.ker r) a :=
  Residue.WittPolynomialResidue.envelopeEquiv_symm p k σ a

theorem envelope_derivative (i : σ) (a : P) :
    envelopeLinearEquiv p k σ (MvPolynomial.pderiv i a) = D i (envelopeLinearEquiv p k σ a) := by
  rw [envelopeLinearEquiv_apply, envelopeLinearEquiv_apply]
  exact (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv_polynomial W σ I δ₀ (RingHom.ker r)
    (EnvelopeThickeningP.EnvelopeThickening.baseIdeal_le_kernel p k B P r hb) i a).symm

def envelopeCompletionEquiv : AdicCompletion I P ≃ₗ[W] AdicCompletion I E :=
  (AdicCompletion.congr I (envelopeLinearEquiv p k σ)).restrictScalars W

def frameCompletionEquiv : AdicCompletion I E ≃ₗ[W] C :=
  PadicFrame.PadicFrameCompletion.equiv p k B E rE
    (EnvelopeThickeningP.EnvelopeThickening.envelopeReduction_surjective p k B P r hr hb)
    (Affine.EnvelopeFrames.AffineEnvelopeFrames.envelope_reduction_base p k B P r hr hb) δE hδE

def completedEquiv : AdicCompletion I P ≃ₗ[W] C :=
  (envelopeCompletionEquiv p k σ).trans (frameCompletionEquiv p k σ)

theorem eval_completedEquiv_of (n : ℕ) (a : P) :
    PD.InverseLimit.PDInverseLimit.eval p k B Tower n (completedEquiv p k σ (AdicCompletion.of I P a)) =
      Affine.EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.coefficient p k B P r hr hb n a := by
  change PD.InverseLimit.PDInverseLimit.eval p k B Tower n
    (frameCompletionEquiv p k σ
      (AdicCompletion.map I (envelopeLinearEquiv p k σ).toLinearMap (AdicCompletion.of I P a))) = _
  rw [AdicCompletion.map_of]
  change PD.InverseLimit.PDInverseLimit.eval p k B Tower n
    (PadicFrame.PadicFrameCompletion.equiv p k B E rE _ _ δE hδE
      (AdicCompletion.of I E (envelopeLinearEquiv p k σ a))) = _
  rw [PadicFrame.PadicFrameCompletion.equiv_of]
  change Ideal.Quotient.mk (PadicPDP.PadicPDThickening.ideal p E n) (envelopeLinearEquiv p k σ a) = _
  rw [envelopeLinearEquiv_apply]
  rfl

theorem envelopeCompletion_derivative (i : σ) (x : AdicCompletion I P) :
    envelopeCompletionEquiv p k σ (AdicCompletion.map I (MvPolynomial.pderiv i).toLinearMap x) =
      AdicCompletion.map I (D i).toLinearMap (envelopeCompletionEquiv p k σ x) := by
  change AdicCompletion.map I (envelopeLinearEquiv p k σ).toLinearMap
      (AdicCompletion.map I (MvPolynomial.pderiv i).toLinearMap x) =
    AdicCompletion.map I (D i).toLinearMap
      (AdicCompletion.map I (envelopeLinearEquiv p k σ).toLinearMap x)
  rw [AdicCompletion.map_comp_apply, AdicCompletion.map_comp_apply]
  have h : (envelopeLinearEquiv p k σ).toLinearMap.comp (MvPolynomial.pderiv i).toLinearMap =
      (D i).toLinearMap.comp (envelopeLinearEquiv p k σ).toLinearMap :=
    LinearMap.ext (envelope_derivative p k σ i)
  rw [h]

theorem completed_derivative (i : σ) (x : AdicCompletion I P) :
    completedEquiv p k σ (AdicCompletion.map I (MvPolynomial.pderiv i).toLinearMap x) =
      L i (completedEquiv p k σ x) := by
  change frameCompletionEquiv p k σ
    (envelopeCompletionEquiv p k σ (AdicCompletion.map I (MvPolynomial.pderiv i).toLinearMap x)) = _
  rw [envelopeCompletion_derivative]
  exact PadicFrame.PadicFrameCompletion.equiv_operator p k B E rE
    (EnvelopeThickeningP.EnvelopeThickening.envelopeReduction_surjective p k B P r hr hb)
    (Affine.EnvelopeFrames.AffineEnvelopeFrames.envelope_reduction_base p k B P r hr hb) δE hδE (D i).toLinearMap (L i)
    (fun n => (Affine.PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.derivation p k B σ r hr hb n i).toLinearMap)
    (fun n a => Affine.PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.derivation_quotient p k B σ r hr hb n i a)
    (fun n a => Affine.PolynomialOperators.AffinePolynomialOperators.eval_derivative p k B σ r hr hb i n a)
    (envelopeCompletionEquiv p k σ x)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.FrameCompletion.WittPolynomialFrameCompletion
