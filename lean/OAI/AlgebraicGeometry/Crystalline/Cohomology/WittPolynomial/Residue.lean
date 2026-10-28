import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.BaseEnvelope
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius

/-! # Residue -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue

noncomputable section

/-! # The actual residue presentation and its polynomial PD envelope -/

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "P" => MvPolynomial σ W
local notation "B" => MvPolynomial σ k
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.reduction p k σ
local notation "I₀" => Ideal.span {(p : W)}
local notation "δ₀" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k

omit [CharP k p] [PerfectRing k p] in
theorem reduction_surjective : Function.Surjective r :=
  MvPolynomial.map_surjective WittVector.constantCoeff (WittVector.constantCoeff_surjective p)

omit [CharP k p] [PerfectRing k p] in
theorem reduction_base : (r).comp (algebraMap W P) = (algebraMap k B).comp WittVector.constantCoeff := by
  apply RingHom.ext
  intro w
  exact MvPolynomial.map_C WittVector.constantCoeff w

theorem reduction_kernel : RingHom.ker r = BasePowers.WittPolynomialBasePowers.ideal p k σ := by
  have hc (w : W) : WittVector.constantCoeff w = 0 ↔ (p : W) ∣ w := by
    rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff]
    rfl
  ext a
  change r a = 0 ↔ a ∈ BasePowers.WittPolynomialBasePowers.ideal p k σ
  rw [BasePowers.WittPolynomialBasePowers.ideal, Ideal.mem_span_singleton]
  simpa only [Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.reduction, map_natCast] using
    (MvPolynomial.C_dvd_iff_map_hom_eq_zero WittVector.constantCoeff (p : W) hc a).symm

def envelopeEquiv : PD.EnvelopeDp.PDEnvelope.Envelope W P I₀ δ₀ (RingHom.ker r) ≃ₐ[P] P := by
  rw [reduction_kernel]
  exact BaseEnvelope.WittPolynomialBaseEnvelope.equiv p k σ

theorem envelopeEquiv_ofAlgebra (a : P) :
    envelopeEquiv p k σ (PD.EnvelopeDp.PDEnvelope.ofAlgebra W P I₀ δ₀ (RingHom.ker r) a) = a :=
  (envelopeEquiv p k σ).commutes a

theorem envelopeEquiv_symm (a : P) :
    (envelopeEquiv p k σ).symm a = PD.EnvelopeDp.PDEnvelope.ofAlgebra W P I₀ δ₀ (RingHom.ker r) a :=
  (envelopeEquiv p k σ).symm_apply_eq.mpr (envelopeEquiv_ofAlgebra p k σ a).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue
