import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation

/-! # Witt -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt

noncomputable section

/-!
# IntegralComparison: the actual truncated Witt divided-power base

Positive powers of the Witt base ideal define quotient rings with proved
divided powers, residue maps, and nilpotence. These are the coefficient
rings for finite polynomial crystalline presentations.
-/

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "J" => Ideal.span {(p : W)}
local notation "δ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k

abbrev Ring (n : ℕ) := AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.Ring W J n

def quotient (n : ℕ) : W →+* Ring p k n := Ideal.Quotient.mk (J ^ (n + 1))

def ideal (n : ℕ) : Ideal (Ring p k n) := AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.ideal W J n

def dividedPowers (n : ℕ) : DividedPowers (ideal p k n) := AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.dividedPowers W J δ n

omit [PerfectRing k p] in
theorem quotient_isDPMorphism (n : ℕ) :
    DividedPowers.IsDPMorphism δ (dividedPowers p k n) (quotient p k n) :=
  AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.quotient_isDPMorphism W J δ n

def reduction (n : ℕ) : Ring p k n →+* k :=
  AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.reduction W J WittVector.constantCoeff WittVector.ker_constantCoeff n

theorem reduction_quotient (n : ℕ) :
    (reduction p k n).comp (quotient p k n) = WittVector.constantCoeff := by
  ext w
  rfl

theorem reduction_surjective (n : ℕ) : Function.Surjective (reduction p k n) :=
  AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.reduction_surjective W J WittVector.constantCoeff WittVector.ker_constantCoeff
    (WittVector.constantCoeff_surjective p) n

theorem reduction_kernel (n : ℕ) : RingHom.ker (reduction p k n) = ideal p k n :=
  AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.reduction_kernel W J WittVector.constantCoeff WittVector.ker_constantCoeff n

omit [CharP k p] [PerfectRing k p] in
theorem prime_power_zero (n : ℕ) : (p : Ring p k n) ^ (n + 1) = 0 := by
  rw [← map_natCast (quotient p k n) p, ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton (p : W))) (n + 1))

omit [CharP k p] [PerfectRing k p] in
theorem prime_nilpotent (n : ℕ) : IsNilpotent (p : Ring p k n) :=
  ⟨n + 1, prime_power_zero p k n⟩

omit [CharP k p] [PerfectRing k p] in
theorem ideal_nilpotent (n : ℕ) : IsNilpotent (ideal p k n) :=
  AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.ideal_isNilpotent W J n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt
