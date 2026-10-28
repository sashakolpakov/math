import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Support
import Mathlib.Algebra.Module.LocalizedModule.Exact

/-! # Localized Module Length -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedModuleLength.Constructions

noncomputable section

/-! Local lengths of actual localized modules form an additive
invariant of short exact sequences. Infinite lengths remain in ENat. -/

universe u v
variable (R : Type u) [CommRing R]

def localLength (M : Type v) [AddCommGroup M] [Module R M] (p : PrimeSpectrum R) : ℕ∞ :=
  Module.length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M)

variable {R} {M N L : Type v} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup L] [Module R L]

theorem localLength_equiv (e : M ≃ₗ[R] N) (p : PrimeSpectrum R) :
    localLength R M p = localLength R N p :=
  (LinearEquiv.ofBijective (LocalizedModule.map p.asIdeal.primeCompl e.toLinearMap)
    ⟨LocalizedModule.map_injective _ _ e.injective,
      LocalizedModule.map_surjective _ _ e.surjective⟩).length_eq

theorem localLength_eq_zero (p : PrimeSpectrum R) (hp : p ∉ Module.support R M) :
    localLength R M p = 0 := by
  let := Module.notMem_support_iff.mp hp
  exact Module.length_eq_zero

theorem localLength_subsingleton [Subsingleton M] (p : PrimeSpectrum R) :
    localLength R M p = 0 := by
  apply localLength_eq_zero
  rw [Module.support_eq_empty]
  exact Set.notMem_empty _

theorem localLength_additivity (f : M →ₗ[R] N) (g : N →ₗ[R] L)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (p : PrimeSpectrum R) :
    localLength R N p = localLength R M p + localLength R L p :=
  Module.length_eq_add_of_exact (LocalizedModule.map p.asIdeal.primeCompl f)
    (LocalizedModule.map p.asIdeal.primeCompl g)
    (LocalizedModule.map_injective _ _ hf) (LocalizedModule.map_surjective _ _ hg)
    (LocalizedModule.map_exact _ f g hfg)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedModuleLength.Constructions
