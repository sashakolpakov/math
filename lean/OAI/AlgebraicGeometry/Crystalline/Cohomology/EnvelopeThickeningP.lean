import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeReduction
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.Thickening
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Site
import Mathlib.Algebra.MvPolynomial.Eval

/-! # Envelope Thickening P -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.EnvelopeThickeningP.EnvelopeThickening

noncomputable section

/-!
# Cohomology: crystalline thickenings constructed from divided-power envelopes

Truncation of a divided-power reduction produces the nilpotent affine
objects required by the crystalline site.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
variable (B : Type u) [CommRing B] [Algebra k B]

omit [Algebra k B] in
theorem p_nilpotent_of_kernel (E : Type u) [CommRing E] [Algebra (WittVector p k) E]
    (r : E →+* B) (δ : DividedPowers (RingHom.ker r))
    (hδ : DividedPowers.IsDPMorphism (Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) δ
      (algebraMap (WittVector p k) E)) (hker : IsNilpotent (RingHom.ker r)) :
    IsNilpotent (p : E) := by
  have hp : (p : E) ∈ RingHom.ker r := by
    have h := hδ.ideal_comp (Ideal.mem_map_of_mem (algebraMap (WittVector p k) E)
      (Ideal.subset_span (Set.mem_singleton (p : WittVector p k))))
    simpa only [map_natCast] using h
  obtain ⟨n, hn⟩ := hker
  exact ⟨n, Ideal.pow_eq_zero_of_mem hn le_rfl hp⟩

def truncate (E : Type u) [CommRing E] [Algebra (WittVector p k) E]
    (r : E →+* B) (hr : Function.Surjective r)
    (hbase : r.comp (algebraMap (WittVector p k) E) = (algebraMap k B).comp WittVector.constantCoeff)
    (δ : DividedPowers (RingHom.ker r))
    (hδ : DividedPowers.IsDPMorphism (Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) δ
      (algebraMap (WittVector p k) E)) (n : ℕ) : PD.Thickening.AffinePDThickening p k B where
  ring := CommRingCat.of (PD.Truncation.PDTruncation.Ring E (RingHom.ker r) n)
  reduction := PD.Truncation.PDTruncation.reduction E (RingHom.ker r) r rfl n
  reduction_surjective := PD.Truncation.PDTruncation.reduction_surjective E (RingHom.ker r) r rfl hr n
  reduction_base := by
    ext w
    change PD.Truncation.PDTruncation.reduction E (RingHom.ker r) r rfl n
      (Ideal.Quotient.mk ((RingHom.ker r) ^ (n + 1)) (algebraMap (WittVector p k) E w)) =
        algebraMap k B (WittVector.constantCoeff w)
    rw [PD.Truncation.PDTruncation.reduction_mk]
    exact DFunLike.congr_fun hbase w
  p_nilpotent := p_nilpotent_of_kernel p k B _ _
    (PD.Truncation.PDTruncation.kernelDividedPowers E (RingHom.ker r) δ r rfl n)
    ((PD.Truncation.PDTruncation.quotient_kernel_isDPMorphism E (RingHom.ker r) δ r rfl n).comp _ hδ)
    (PD.Truncation.PDTruncation.kernel_isNilpotent E (RingHom.ker r) r rfl n)
  dividedPowers := PD.Truncation.PDTruncation.kernelDividedPowers E (RingHom.ker r) δ r rfl n
  baseDP := (PD.Truncation.PDTruncation.quotient_kernel_isDPMorphism E (RingHom.ker r) δ r rfl n).comp _ hδ

/-- A version of truncation with the divided-power ideal specified separately. -/
def truncateIdeal (E : Type u) [CommRing E] [Algebra (WittVector p k) E]
    (r : E →+* B) (hr : Function.Surjective r)
    (hbase : r.comp (algebraMap (WittVector p k) E) = (algebraMap k B).comp WittVector.constantCoeff)
    (J : Ideal E) (hker : RingHom.ker r = J) (δ : DividedPowers J)
    (hδ : DividedPowers.IsDPMorphism (Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) δ
      (algebraMap (WittVector p k) E)) (n : ℕ) : PD.Thickening.AffinePDThickening p k B where
  ring := CommRingCat.of (PD.Truncation.PDTruncation.Ring E J n)
  reduction := PD.Truncation.PDTruncation.reduction E J r hker n
  reduction_surjective := PD.Truncation.PDTruncation.reduction_surjective E J r hker hr n
  reduction_base := by
    ext w
    change PD.Truncation.PDTruncation.reduction E J r hker n
      (Ideal.Quotient.mk (J ^ (n + 1)) (algebraMap (WittVector p k) E w)) =
        algebraMap k B (WittVector.constantCoeff w)
    rw [PD.Truncation.PDTruncation.reduction_mk]
    exact DFunLike.congr_fun hbase w
  p_nilpotent := p_nilpotent_of_kernel p k B _ _
    (PD.Truncation.PDTruncation.kernelDividedPowers E J δ r hker n)
    ((PD.Truncation.PDTruncation.quotient_kernel_isDPMorphism E J δ r hker n).comp _ hδ)
    (PD.Truncation.PDTruncation.kernel_isNilpotent E J r hker n)
  dividedPowers := PD.Truncation.PDTruncation.kernelDividedPowers E J δ r hker n
  baseDP := (PD.Truncation.PDTruncation.quotient_kernel_isDPMorphism E J δ r hker n).comp _ hδ

section Envelope

variable (A : Type u) [CommRing A] [Algebra (WittVector p k) A]
variable (r : A →+* B) (hr : Function.Surjective r)
variable (hbase : r.comp (algebraMap (WittVector p k) A) =
  (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k
local notation "I₀" => Ideal.span {(p : W)}
local notation "δ₀" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope W A I₀ δ₀ (RingHom.ker r)
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal W A I₀ δ₀ (RingHom.ker r)

include hbase in
theorem baseIdeal_le_kernel : (I₀).map (algebraMap W A) ≤ RingHom.ker r := by
  rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
  rintro w (rfl : w = (p : W))
  change r (algebraMap W A (p : W)) = 0
  have h := DFunLike.congr_fun hbase (p : W)
  change r (algebraMap W A (p : W)) = algebraMap k B (WittVector.constantCoeff (p : W)) at h
  have hp : WittVector.constantCoeff (p : W) = (0 : k) := by
    rw [map_natCast, CharP.cast_eq_zero]
  simpa only [hp, map_zero] using h

/-- Reduction of the relative envelope to the specified residual algebra. -/
def envelopeReduction : E →+* B :=
  (r.quotientKerEquivOfSurjective hr).toRingHom.comp
    (PD.EnvelopeReduction.PDEnvelopeReduction.reduction W A I₀ δ₀ (RingHom.ker r)
      (baseIdeal_le_kernel p k B A r hbase)).toRingHom

@[simp]
theorem envelopeReduction_ofAlgebra (a : A) :
    envelopeReduction p k B A r hr hbase (PD.EnvelopeDp.PDEnvelope.ofAlgebra W A I₀ δ₀ (RingHom.ker r) a) = r a := by
  change r.quotientKerEquivOfSurjective hr
    (PD.EnvelopeReduction.PDEnvelopeReduction.reduction W A I₀ δ₀ (RingHom.ker r)
      (baseIdeal_le_kernel p k B A r hbase) (PD.EnvelopeDp.PDEnvelope.ofAlgebra W A I₀ δ₀ (RingHom.ker r) a)) = r a
  rw [PD.EnvelopeReduction.PDEnvelopeReduction.reduction_ofAlgebra, RingHom.quotientKerEquivOfSurjective_apply_mk]

theorem envelopeReduction_surjective :
    Function.Surjective (envelopeReduction p k B A r hr hbase) :=
  (r.quotientKerEquivOfSurjective hr).surjective.comp
    (PD.EnvelopeReduction.PDEnvelopeReduction.reduction_surjective W A I₀ δ₀ (RingHom.ker r)
      (baseIdeal_le_kernel p k B A r hbase))

theorem envelopeReduction_kernel : RingHom.ker (envelopeReduction p k B A r hr hbase) = J := by
  calc
    _ = RingHom.ker (PD.EnvelopeReduction.PDEnvelopeReduction.reduction W A I₀ δ₀ (RingHom.ker r)
        (baseIdeal_le_kernel p k B A r hbase)).toRingHom :=
      RingHom.ker_comp_of_injective _ (r.quotientKerEquivOfSurjective hr).injective
    _ = J := PD.EnvelopeReduction.PDEnvelopeReduction.reduction_kernel W A I₀ δ₀ (RingHom.ker r)
      (baseIdeal_le_kernel p k B A r hbase)

/-- A genuine nilpotent crystalline thickening produced from any affine
lift of the residual algebra, using the constructed relative PD envelope. -/
def fromEnvelope (n : ℕ) : PD.Thickening.AffinePDThickening p k B := by
  let : Algebra W E :=
    ((PD.EnvelopeDp.PDEnvelope.ofAlgebra W A I₀ δ₀ (RingHom.ker r)).comp (algebraMap W A)).toAlgebra
  refine truncateIdeal p k B E (envelopeReduction p k B A r hr hbase)
    (envelopeReduction_surjective p k B A r hr hbase) ?_
    J (envelopeReduction_kernel p k B A r hr hbase)
    (PD.EnvelopeDp.PDEnvelope.dividedPowers W A I₀ δ₀ (RingHom.ker r)) ?_ n
  · ext w
    change envelopeReduction p k B A r hr hbase
      (PD.EnvelopeDp.PDEnvelope.ofAlgebra W A I₀ δ₀ (RingHom.ker r) (algebraMap W A w)) =
        algebraMap k B (WittVector.constantCoeff w)
    rw [envelopeReduction_ofAlgebra]
    exact DFunLike.congr_fun hbase w
  · exact PD.EnvelopeDp.PDEnvelope.base_isDPMorphism W A I₀ δ₀ (RingHom.ker r)
      (baseIdeal_le_kernel p k B A r hbase)

end Envelope

/-- A canonical polynomial presentation over the Witt base. -/
def polynomialReduction : MvPolynomial B (WittVector p k) →+* B :=
  MvPolynomial.eval₂Hom ((algebraMap k B).comp WittVector.constantCoeff) id

omit [CharP k p] in
theorem polynomialReduction_surjective : Function.Surjective (polynomialReduction p k B) := by
  intro b
  exact ⟨MvPolynomial.X b, MvPolynomial.eval₂Hom_X' _ _ _⟩

omit [CharP k p] in
theorem polynomialReduction_base :
    (polynomialReduction p k B).comp (algebraMap (WittVector p k) (MvPolynomial B (WittVector p k))) =
      (algebraMap k B).comp WittVector.constantCoeff := by
  ext w
  exact MvPolynomial.eval₂Hom_C _ _ _

/-- Nilpotent divided-power thickenings exist for every residual algebra,
using its canonical polynomial presentation. -/
def polynomialThickening (n : ℕ) : PD.Thickening.AffinePDThickening p k B :=
  fromEnvelope p k B (MvPolynomial B (WittVector p k))
    (polynomialReduction p k B) (polynomialReduction_surjective p k B)
    (polynomialReduction_base p k B) n

/-- Attach the constructed thickening to an actual affine open of the special fibre. -/
def objectFromAffineOpen (X : Over (Spec (CommRingCat.of k)))
    (j : Spec (CommRingCat.of B) ⟶ X.left) [IsOpenImmersion j]
    (hj : j ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k B)))
    (n : ℕ) : Site.Object p k X where
  residueRing := CommRingCat.of B
  thickening := polynomialThickening p k B n
  immersion := j
  over_base := hj

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.EnvelopeThickeningP.EnvelopeThickening
