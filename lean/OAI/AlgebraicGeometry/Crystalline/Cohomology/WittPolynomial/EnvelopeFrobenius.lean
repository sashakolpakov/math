import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames
import OAI.AlgebraicGeometry.Crystalline.Cohomology.TorsionFreeDP
import Mathlib.Algebra.CharP.Algebra

/-! # Envelope Frobenius -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.EnvelopeFrobenius.WittPolynomialEnvelopeFrobenius

noncomputable section

/-! # The absolute-Frobenius lift on the original polynomial PD envelope -/

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
local notation "e" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.envelopeEquiv p k σ
local notation "rE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.EnvelopeThickeningP.EnvelopeThickening.envelopeReduction p k B P r hr hb
local notation "δE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.envelopeDP p k B P r hr hb
local notation "φ" => WittVector.frobeniusEquiv p k

local instance envelopeBaseAlgebra : Algebra W E :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra W P I δ₀ (RingHom.ker r)).comp (algebraMap W P)).toAlgebra

instance envelope_isDomain : IsDomain E := MulEquiv.isDomain P (e).toRingEquiv.toMulEquiv

instance envelope_charZero : CharZero E :=
  charZero_of_injective_ringHom (f := (e).symm.toRingHom) (e).symm.injective

theorem ofAlgebra_surjective : Function.Surjective (PD.EnvelopeDp.PDEnvelope.ofAlgebra W P I δ₀ (RingHom.ker r)) := by
  intro x
  exact ⟨e x, (Residue.WittPolynomialResidue.envelopeEquiv_symm p k σ (e x)).symm.trans ((e).symm_apply_apply x)⟩

def map : E →+* E :=
  (e).symm.toRingHom.comp ((Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.lift p k σ).comp (e).toRingHom)

theorem map_ofAlgebra (a : P) :
    map p k σ (PD.EnvelopeDp.PDEnvelope.ofAlgebra W P I δ₀ (RingHom.ker r) a) =
      PD.EnvelopeDp.PDEnvelope.ofAlgebra W P I δ₀ (RingHom.ker r) (Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.lift p k σ a) := by
  change (e).symm (Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.lift p k σ
    (e (PD.EnvelopeDp.PDEnvelope.ofAlgebra W P I δ₀ (RingHom.ker r) a))) = _
  rw [Residue.WittPolynomialResidue.envelopeEquiv_ofAlgebra, Residue.WittPolynomialResidue.envelopeEquiv_symm]

theorem map_base (w : W) :
    map p k σ (algebraMap W E w) = algebraMap W E ((φ).toRingHom w) := by
  change map p k σ (PD.EnvelopeDp.PDEnvelope.ofAlgebra W P I δ₀ (RingHom.ker r) (algebraMap W P w)) = _
  rw [map_ofAlgebra, Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.lift_base]
  rfl

theorem reduction_map (x : E) : rE (map p k σ x) = frobenius B p (rE x) := by
  obtain ⟨a, rfl⟩ := ofAlgebra_surjective p k σ x
  rw [map_ofAlgebra, EnvelopeThickeningP.EnvelopeThickening.envelopeReduction_ofAlgebra,
    EnvelopeThickeningP.EnvelopeThickening.envelopeReduction_ofAlgebra]
  exact DFunLike.congr_fun (Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.reduction_lift p k σ) a

theorem map_isDPMorphism : DividedPowers.IsDPMorphism δE δE (map p k σ) :=
  TorsionFreeDP.TorsionFreeDPMorphism.isDPMorphism (RingHom.ker rE) δE (RingHom.ker rE) δE (map p k σ)
    (Ideal.map_le_iff_le_comap.mpr (by
      intro x hx
      change rE (map p k σ x) = 0
      rw [reduction_map, show rE x = 0 from hx, map_zero]))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.EnvelopeFrobenius.WittPolynomialEnvelopeFrobenius
