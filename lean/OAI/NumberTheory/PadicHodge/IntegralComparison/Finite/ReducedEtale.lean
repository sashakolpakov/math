import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.Algebra.CharP.Reduced
import Mathlib.RingTheory.FinitePresentation

/-! # Reduced Etale -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.ReducedEtale

noncomputable section

/-! Finite reduced algebras in positive characteristic have zero differentials and are étale over a field. -/

universe u v

variable (p : ℕ) [Fact p.Prime] (R : Type u) (A : Type v) [CommRing R] [CommRing A]
  [Algebra R A] [Finite A] [IsReduced A] [CharP A p]

include p in
theorem differential_zero (a : A) : KaehlerDifferential.D R A a = 0 := by
  obtain ⟨b, hb⟩ := Finite.surjective_of_injective (frobenius_inj A p) a
  change b ^ p = a at hb
  rw [← hb, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul A, CharP.cast_eq_zero A p, zero_smul]

include p in
theorem formallyUnramified : Algebra.FormallyUnramified R A := by
  constructor
  suffices (⊤ : Submodule A (KaehlerDifferential R A)) ≤ ⊥ from
    (subsingleton_iff_forall_eq 0).mpr (fun x => this trivial)
  rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact differential_zero p R A a

include p in
theorem etale (k : Type u) [Field k] [Algebra k A] : Algebra.Etale k A := by
  let : Module.Finite k A := inferInstance
  let : Algebra.FinitePresentation k A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.FormallyUnramified k A := formallyUnramified p k A
  exact Algebra.Etale.of_formallyUnramified_of_flat

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.ReducedEtale
