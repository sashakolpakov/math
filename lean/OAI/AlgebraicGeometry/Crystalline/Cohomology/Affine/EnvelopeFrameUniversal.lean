import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames

/-! # Envelope Frame Universal -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal

noncomputable section

/-!
# The universal property of the actual p-power envelope frames

The polynomial-presentation coefficients map into each genuine frame
level. A prescribed lift of those coefficients to a crystalline ring
extends uniquely to a native divided-power map whenever that level's
power of p vanishes. The uniqueness is proved from the original PD
envelope universal property and the actual quotient map.
-/

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (B : Type u) [CommRing B] [Algebra k B]
  (A : Type u) [CommRing A] [Algebra (WittVector p k) A]
  (r : A →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) A) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k
local notation "I₀" => Ideal.span {(p : W)}
local notation "δ₀" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope W A I₀ δ₀ (RingHom.ker r)
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal W A I₀ δ₀ (RingHom.ker r)
local notation "δ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers W A I₀ δ₀ (RingHom.ker r)
local notation "rE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.EnvelopeThickeningP.EnvelopeThickening.envelopeReduction p k B A r hr hbase

local instance envelopeBaseAlgebra : Algebra W E :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra W A I₀ δ₀ (RingHom.ker r)).comp (algebraMap W A)).toAlgebra

def coefficient (n : ℕ) : A →+* (EnvelopeFrames.AffineEnvelopeFrames.frame p k B A r hr hbase n).ring :=
  (Ideal.Quotient.mk (PadicPDP.PadicPDThickening.ideal p E n)).comp (PD.EnvelopeDp.PDEnvelope.ofAlgebra W A I₀ δ₀ (RingHom.ker r))

def coefficientAlgHom (n : ℕ) : A →ₐ[W] (EnvelopeFrames.AffineEnvelopeFrames.frame p k B A r hr hbase n).ring where
  __ := coefficient p k B A r hr hbase n
  commutes' _ := rfl

theorem coefficient_reduction (n : ℕ) (b : A) :
    (EnvelopeFrames.AffineEnvelopeFrames.frame p k B A r hr hbase n).reduction (coefficient p k B A r hr hbase n b) = r b :=
  EnvelopeThickeningP.EnvelopeThickening.envelopeReduction_ofAlgebra p k B A r hr hbase b

theorem p_pow_eq_zero (n : ℕ) : (p : (EnvelopeFrames.AffineEnvelopeFrames.frame p k B A r hr hbase n).ring) ^ (n + 1) = 0 :=
  PadicPDP.PadicPDThickening.p_pow_eq_zero p E n

theorem quotient_isDPMorphism (n : ℕ) :
    DividedPowers.IsDPMorphism δ (EnvelopeFrames.AffineEnvelopeFrames.frame p k B A r hr hbase n).dividedPowers
      (Ideal.Quotient.mk (PadicPDP.PadicPDThickening.ideal p E n)) := by
  have hi : DividedPowers.IsDPMorphism δ (EnvelopeFrames.AffineEnvelopeFrames.envelopeDP p k B A r hr hbase)
      (RingHom.id E) :=
    { ideal_comp := by
        rw [Ideal.map_id, EnvelopeThickeningP.EnvelopeThickening.envelopeReduction_kernel]
      dpow_comp := fun _ _ => rfl }
  exact (PadicPDP.PadicPDThickening.quotient_isDPMorphism p k B E rE
    (EnvelopeFrames.AffineEnvelopeFrames.envelopeDP p k B A r hr hbase)
    (EnvelopeFrames.AffineEnvelopeFrames.envelope_baseDP p k B A r hr hbase) n).comp _ hi

variable (C : Type u) [CommRing C] [Algebra k C] (S : PD.Thickening.AffinePDThickening p k C)
  (f : B →ₐ[k] C) (l : A →ₐ[WittVector p k] S.ring)
  (hl : S.reduction.comp l.toRingHom = f.toRingHom.comp r)
  (n : ℕ) (hn : (p : S.ring) ^ (n + 1) = 0)

theorem frameMap_coefficient (b : A) :
    EnvelopeFrames.AffineEnvelopeFrames.frameMap p k B A r hr hbase C S f l hl n hn
      (coefficient p k B A r hr hbase n b) = l b :=
  PD.EnvelopeDp.PDEnvelope.evaluate_ofAlgebra W A I₀ δ₀ (RingHom.ker r)
    (EnvelopeFrames.AffineEnvelopeFrames.target p k B A r C S f l hl) b

theorem frameMap_unique (g : (EnvelopeFrames.AffineEnvelopeFrames.frame p k B A r hr hbase n).ring →ₐ[W] S.ring)
    (hg : DividedPowers.IsDPMorphism (EnvelopeFrames.AffineEnvelopeFrames.frame p k B A r hr hbase n).dividedPowers
      S.dividedPowers g.toRingHom)
    (hc : ∀ b, g (coefficient p k B A r hr hbase n b) = l b) :
    g = EnvelopeFrames.AffineEnvelopeFrames.frameMap p k B A r hr hbase C S f l hl n hn := by
  let T := EnvelopeFrames.AffineEnvelopeFrames.target p k B A r C S f l hl
  let e : E →ₐ[A] T.ring :=
    { __ := g.toRingHom.comp (Ideal.Quotient.mk (PadicPDP.PadicPDThickening.ideal p E n))
      commutes' := hc }
  have he := PD.EnvelopeDp.PDEnvelope.lift_unique W A I₀ δ₀ (RingHom.ker r) T e
    (hg.comp _ (quotient_isDPMorphism p k B A r hr hbase n))
  apply AlgHom.ext
  intro x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun he z

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal
