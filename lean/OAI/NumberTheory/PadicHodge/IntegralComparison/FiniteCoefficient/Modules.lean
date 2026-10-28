import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Modules -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.Modules

noncomputable section

/-!
# IntegralComparison: finite generation over a finite coefficient quotient implies finiteness
-/

universe u v w

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Finite S]
  (M : Type w) [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem finite (f : R →+* S) (hf : Function.Surjective f)
    (hk : ∀ r, f r = 0 → ∀ x : M, r • x = 0) : Finite M := by
  let : Finite (R ⧸ RingHom.ker f) :=
    Finite.of_injective _ (RingHom.quotientKerEquivOfSurjective hf).injective
  have hI : Module.IsTorsionBySet R M (RingHom.ker f) :=
    fun {x} {a} => hk a.val a.property x
  let := hI.module
  let : Module.Finite (R ⧸ RingHom.ker f) M :=
    Module.Finite.of_surjective hI.semilinearMap Function.surjective_id
  exact Module.finite_of_finite (R ⧸ RingHom.ker f)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.Modules
