import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # Flat Union -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.FlatUnion

/-! # Flatness from finite families contained in embedded flat modules -/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {ι : Type*} (N : ι → Type*) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  (f : ∀ i, N i →ₗ[R] M)

theorem flat [∀ i, Module.Flat R (N i)]
    (hf : ∀ i, Function.Injective (f i))
    (hlift : ∀ {n : ℕ} (x : Fin n → M), ∃ i, ∃ y : Fin n → N i, ∀ j, f i (y j) = x j) :
    Module.Flat R M := by
  classical
  apply Module.Flat.of_forall_isTrivialRelation
  intro n a x hax
  obtain ⟨i, y, hy⟩ := hlift x
  have hrel : ∑ j, a j • y j = 0 := by
    apply hf i
    simpa only [map_sum, map_smul, hy, map_zero] using hax
  obtain ⟨k, b, z, hz, hab⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  refine ⟨k, b, fun j => f i (z j), ?_, hab⟩
  intro j
  have he := congrArg (f i) (hz j)
  simpa only [hy, map_sum, map_smul] using he

end OAI.NumberTheory.PadicHodge.PeriodInvariants.FlatUnion
