import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.FrameFrobenius
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.Levels

/-! # Frame Frobenius Coordinates -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.FrameFrobeniusCoordinates.WittPolynomialFrameFrobeniusCoordinates

noncomputable section

/-! # The original polynomial frame Frobenius on its canonical coordinates -/

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "P" => MvPolynomial σ W
local notation "B" => MvPolynomial σ k
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.reduction p k σ
local notation "hr" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_surjective p k σ
local notation "hb" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_base p k σ
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope W P I γ (RingHom.ker r)

theorem coefficient (n : ℕ) (f : P) :
    FrameFrobenius.WittPolynomialFrameFrobenius.levelMap p k σ n
      (Affine.EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.coefficient p k B P r hr hb n f) =
    Affine.EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.coefficient p k B P r hr hb n
      (Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.lift p k σ f) := by
  let q := Ideal.Quotient.mk (PadicPDP.PadicPDThickening.ideal p E n)
  exact congrArg q (EnvelopeFrobenius.WittPolynomialEnvelopeFrobenius.map_ofAlgebra p k σ f)

theorem coordinate (n : ℕ) (i : σ) :
    FrameFrobenius.WittPolynomialFrameFrobenius.levelMap p k σ n
      ((FramedPolynomial.Levels.FramedPolynomialLevels.level p k B σ r hr hb n).coordinate i) =
    ((FramedPolynomial.Levels.FramedPolynomialLevels.level p k B σ r hr hb n).coordinate i) ^ p := by
  let c := Affine.EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.coefficient p k B P r hr hb n
  have h₁ := coefficient p k σ n (MvPolynomial.X i)
  have h₂ := congrArg c (Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.lift_X p k σ i)
  exact h₁.trans (h₂.trans (map_pow c (MvPolynomial.X i) p))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.FrameFrobeniusCoordinates.WittPolynomialFrameFrobeniusCoordinates
