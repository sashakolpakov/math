import OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteProductTrace
import OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteEtaleIntegralTrace

/-! # Etale Field Trace Pairing -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleFieldTracePairing.Finite

noncomputable section

/-! # The trace pairing of a finite étale algebra over a field is nondegenerate -/

universe u

theorem product_single (K : Type u) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι]
    (L : ι → Type u) [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
    [∀ i, FiniteDimensional K (L i)] (x : ∀ i, L i) (i : ι) (y : L i) :
    Algebra.trace K (∀ i, L i) (x * Pi.single i y) = Algebra.trace K (L i) (x i * y) := by
  classical
  rw [FiniteProductTrace.of_field, Finset.sum_eq_single i]
  · rw [Pi.mul_apply, Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.mul_apply, Pi.single_eq_of_ne hji, mul_zero, map_zero]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

variable (K E : Type u) [Field K] [CommRing E] [Algebra K E] [Algebra.Etale K E]

theorem separates : (Algebra.traceForm K E).SeparatingLeft := by
  classical
  obtain ⟨ι, _, L, hL, hKL, e, hfin⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K E).mp inferInstance
  let : Fintype ι := Fintype.ofFinite ι
  let : ∀ i, Field (L i) := hL
  let : ∀ i, Algebra K (L i) := hKL
  have : ∀ i, FiniteDimensional K (L i) := fun i => (hfin i).1
  have : ∀ i, Algebra.IsSeparable K (L i) := fun i => (hfin i).2
  intro x hx
  apply e.injective
  rw [map_zero]
  funext i
  apply (traceForm_nondegenerate K (L i)).1 (e x i)
  intro y
  have he := hx (e.symm (Pi.single i y))
  change Algebra.trace K E (x * e.symm (Pi.single i y)) = 0 at he
  rw [← Algebra.trace_eq_of_algEquiv e, map_mul, AlgEquiv.apply_symm_apply, product_single] at he
  exact he

theorem nondegenerate : (Algebra.traceForm K E).Nondegenerate := by
  refine ⟨separates K E, ?_⟩
  intro y hy
  apply separates K E y
  intro x
  change Algebra.trace K E (y * x) = 0
  rw [mul_comm]
  exact hy x

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleFieldTracePairing.Finite
