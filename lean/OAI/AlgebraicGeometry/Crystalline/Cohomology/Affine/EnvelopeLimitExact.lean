import OAI.AlgebraicGeometry.Crystalline.Cohomology.PDInverseLimitExact
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames

/-! # Envelope Limit Exact -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeLimitExact.AffineEnvelopeLimitExact

noncomputable section

/-!
# The exact completion sequence for actual affine PD envelopes

Specializing the proved p-power quotient result to the constructed relative
PD envelope gives a short exact sequence beginning with its original
compatible-section ring. No extra condition on the affine presentation
or on the transition maps is introduced.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k B A : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] [CommRing A] [Algebra (WittVector p k) A]
  (r : A →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) A) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k
local notation "I₀" => Ideal.span {(p : W)}
local notation "δ₀" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope W A I₀ δ₀ (RingHom.ker r)

local instance envelopeBaseAlgebra : Algebra W E :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra W A I₀ δ₀ (RingHom.ker r)).comp (algebraMap W A)).toAlgebra

theorem shortExact :
    (PD.InverseLimitExact.PDInverseLimitExact.sequence p k B (EnvelopeFrames.AffineEnvelopeFrames.tower p k B A r hr hbase)).ShortExact :=
  PDInverseLimitExact.PadicPDInverseLimitExact.shortExact p k B _ _
    (EnvelopeThickeningP.EnvelopeThickening.envelopeReduction_surjective p k B A r hr hbase)
    (EnvelopeFrames.AffineEnvelopeFrames.envelope_reduction_base p k B A r hr hbase)
    (EnvelopeFrames.AffineEnvelopeFrames.envelopeDP p k B A r hr hbase)
    (EnvelopeFrames.AffineEnvelopeFrames.envelope_baseDP p k B A r hr hbase)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeLimitExact.AffineEnvelopeLimitExact
