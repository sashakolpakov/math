import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequenceReduction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.QuotientSupport

/-! # Sequence Prime Reduction -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequencePrimeReduction

noncomputable section

/-! Prime factors in a regular-sequence Euler pairing admit a parameter
outside the prime unless the factor is supported at the closed point.
All quotient identifications here are native module equivalences. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory

universe u

open RingTheory.Sequence OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequenceModule

variable (R : Type u) [CommRing R]

def permutationEquiv (rs ss : List R) (h : rs.Perm ss) : SequenceModule.quotient R rs ≃ₗ[R] SequenceModule.quotient R ss := by
  have hI : Ideal.ofList rs = Ideal.ofList ss := congrArg Ideal.span (Set.ext fun _ => h.mem_iff)
  exact Submodule.quotEquivOfEq _ _ hI

theorem prime_support (p : PrimeSpectrum R) :
    Module.support R (R ⧸ p.asIdeal) = PrimeSpectrum.zeroLocus p.asIdeal := by
  rw [Module.support_of_algebra, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]

theorem prime_mem (p : PrimeSpectrum R) : p ∈ Module.support R (R ⧸ p.asIdeal) := by
  rw [prime_support]
  exact (le_rfl : p.asIdeal ≤ p.asIdeal)

theorem closed_support [IsLocalRing R] :
    Module.support R (R ⧸ (IsLocalRing.closedPoint R).asIdeal) ⊆ {IsLocalRing.closedPoint R} := by
  rw [prime_support]
  intro p hp
  apply Set.mem_singleton_iff.mpr
  apply PrimeSpectrum.ext
  apply le_antisymm
  · exact IsLocalRing.le_maximalIdeal p.isPrime.ne_top
  · exact hp

theorem prime_regular (p : PrimeSpectrum R) (r : R) (hr : r ∉ p.asIdeal) :
    IsSMulRegular (R ⧸ p.asIdeal) r := by
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro m hm
  change Ideal.Quotient.mk p.asIdeal r * m = 0 at hm
  exact (mul_eq_zero.mp hm).resolve_left (fun h => hr (Ideal.Quotient.eq_zero_iff_mem.mp h))

theorem exists_parameter [IsLocalRing R] (rs : List R) (p : PrimeSpectrum R)
    (hp : p ≠ IsLocalRing.closedPoint R)
    (hiso : Module.support R (R ⧸ p.asIdeal) ∩ Module.support R (SequenceModule.quotient R rs) ⊆
      {IsLocalRing.closedPoint R}) :
    ∃ r ∈ rs, r ∉ p.asIdeal := by
  classical
  by_contra! h
  apply hp
  apply Set.mem_singleton_iff.mp
  apply hiso
  refine ⟨prime_mem R p, ?_⟩
  rw [SequenceModule.support]
  exact Ideal.span_le.mpr h

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequencePrimeReduction
