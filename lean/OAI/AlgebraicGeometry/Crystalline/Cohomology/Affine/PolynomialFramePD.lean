import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameDerivatives
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SurjectivePD

/-! # Polynomial Frame PD -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFramePD.AffinePolynomialFramePD

noncomputable section

/-!
# The PD rule for derivatives of the original affine frame

The original frame divided powers are descended from the universal
envelope. The quotient chain rule therefore gives the PD derivation
identity for the coordinate derivatives on every actual frame level.
-/

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k
local notation "Poly" => MvPolynomial σ W
local notation "I₀" => Ideal.span {(p : W)}
local notation "δ₀" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope W Poly I₀ δ₀ (RingHom.ker r)
local notation "rE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.EnvelopeThickeningP.EnvelopeThickening.envelopeReduction p k B Poly r hr hbase
local notation "δE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.envelopeDP p k B Poly r hr hbase
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.frame p k B Poly r hr hbase
local notation "q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.quotient p k B σ r hr hbase
local notation "dE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.source p k B σ r hbase
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.derivation p k B σ r hr hbase

local instance envelopeBaseAlgebra : Algebra W E :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra W Poly I₀ δ₀ (RingHom.ker r)).comp (algebraMap W Poly)).toAlgebra

theorem quotient_ideal (n : ℕ) :
    (RingHom.ker rE).map (q n).toRingHom = RingHom.ker (T n).reduction :=
  (PadicPDP.PadicPDThickening.reduction_kernel p k B E rE δE
    (EnvelopeFrames.AffineEnvelopeFrames.envelope_baseDP p k B Poly r hr hbase) n).symm

theorem quotient_isDPMorphism (n : ℕ) :
    DividedPowers.IsDPMorphism δE (T n).dividedPowers (q n).toRingHom :=
  PadicPDP.PadicPDThickening.quotient_isDPMorphism p k B E rE δE
    (EnvelopeFrames.AffineEnvelopeFrames.envelope_baseDP p k B Poly r hr hbase) n

theorem source_dpow (i : σ) (m : ℕ) (a : E) (ha : a ∈ RingHom.ker rE) :
    dE i ((δE).dpow (m + 1) a) = (δE).dpow m a * dE i a := by
  have ha' : a ∈ PD.EnvelopeDp.PDEnvelope.ideal W Poly I₀ δ₀ (RingHom.ker r) :=
    EnvelopeThickeningP.EnvelopeThickening.envelopeReduction_kernel p k B Poly r hr hbase ▸ ha
  exact Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv_dpow W σ I₀ δ₀ (RingHom.ker r)
    (EnvelopeThickeningP.EnvelopeThickening.baseIdeal_le_kernel p k B Poly r hbase) i m ha'

theorem dpow (n : ℕ) (i : σ) (m : ℕ) (a : (T n).ring)
    (ha : a ∈ RingHom.ker (T n).reduction) :
    D n i ((T n).dividedPowers.dpow (m + 1) a) =
      (T n).dividedPowers.dpow m a * D n i a :=
  SurjectivePD.SurjectivePDDerivation.dpow W E (T n).ring (RingHom.ker rE)
    (RingHom.ker (T n).reduction) δE (T n).dividedPowers (q n)
    Ideal.Quotient.mk_surjective (quotient_ideal p k B σ r hr hbase n)
    (quotient_isDPMorphism p k B σ r hr hbase n) (dE i) (D n i)
    (source_dpow p k B σ r hr hbase i)
    (PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.derivation_quotient p k B σ r hr hbase n i) m a ha

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFramePD.AffinePolynomialFramePD
