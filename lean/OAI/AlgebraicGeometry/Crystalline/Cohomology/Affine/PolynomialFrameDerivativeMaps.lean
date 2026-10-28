import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeMapDerivatives

/-! # Polynomial Frame Derivative Maps -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameDerivativeMaps.AffinePolynomialFrameDerivativeMaps

noncomputable section

/-!
# Derivatives commute with coordinate-preserving evaluation of the frame

The universal PD chain rule identifies differentiation after evaluation
with evaluation after differentiation, including all divided-power
elements of the original p-power envelope quotient.
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
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.frame p k B Poly r hr hbase
local notation "q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.quotient p k B σ r hr hbase
local notation "d" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.derivation p k B σ r hr hbase

local instance envelopeBaseAlgebra : Algebra W E :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra W Poly I₀ δ₀ (RingHom.ker r)).comp (algebraMap W Poly)).toAlgebra

variable (C : Type u) [CommRing C] [Algebra k C] (S : PD.Thickening.AffinePDThickening p k C)
  (f : B →ₐ[k] C) (l : MvPolynomial σ (WittVector p k) →ₐ[WittVector p k] S.ring)
  (hl : S.reduction.comp l.toRingHom = f.toRingHom.comp r)
  (D : Derivation (WittVector p k) S.ring S.ring)
  (hD : ∀ m a, a ∈ RingHom.ker S.reduction →
    D (S.dividedPowers.dpow (m + 1) a) = S.dividedPowers.dpow m a * D a)
  (i : σ) [DecidableEq σ]
  (hc : ∀ j, D (l (MvPolynomial.X j)) = if j = i then 1 else 0)

include hD hc in
theorem naturality (n : ℕ) (hn : (p : S.ring) ^ (n + 1) = 0) (a : (T n).ring) :
    D (EnvelopeFrames.AffineEnvelopeFrames.frameMap p k B Poly r hr hbase C S f l hl n hn a) =
      EnvelopeFrames.AffineEnvelopeFrames.frameMap p k B Poly r hr hbase C S f l hl n hn (d n i a) := by
  let g := EnvelopeFrames.AffineEnvelopeFrames.frameMap p k B Poly r hr hbase C S f l hl n hn
  let e : E →ₐ[W] S.ring := g.comp (q n)
  have he : DividedPowers.IsDPMorphism
      (PD.EnvelopeDp.PDEnvelope.dividedPowers W Poly I₀ δ₀ (RingHom.ker r)) S.dividedPowers e.toRingHom :=
    (EnvelopeFrames.AffineEnvelopeFrames.frameMap_isDPMorphism p k B Poly r hr hbase C S f l hl n hn).comp _
      (PolynomialFrameForms.AffinePolynomialFrameForms.quotient_isDPMorphism p k B σ r hr hbase n)
  have hcoord (j : σ) : D (e (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.coordinate W σ I₀ δ₀ (RingHom.ker r) j)) =
      if j = i then 1 else 0 := by
    change D (g (EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.coefficient p k B Poly r hr hbase n (MvPolynomial.X j))) = _
    rw [EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.frameMap_coefficient]
    exact hc j
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change D (e a) = g (d n i (q n a))
  rw [PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.derivation_quotient]
  exact Polynomial.EnvelopeMapDerivatives.PolynomialEnvelopeMapDerivatives.naturality W σ I₀ δ₀ (RingHom.ker r)
    (EnvelopeThickeningP.EnvelopeThickening.baseIdeal_le_kernel p k B Poly r hbase) S.ring
    (RingHom.ker S.reduction) S.dividedPowers e he D hD i hcoord a

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameDerivativeMaps.AffinePolynomialFrameDerivativeMaps
