import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.Algebra.Regular.SMul
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Power Module Sequence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PowerModuleSequence

noncomputable section

/-! Exact sequences for successive principal-ideal quotients of a regular module. -/

open _root_.CategoryTheory
open scoped Pointwise

universe u v

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (r : R)

abbrev submodule (n : ℕ) : Submodule R M := (Ideal.span {r}) ^ n • ⊤
abbrev Quotient (n : ℕ) := M ⧸ submodule R M r n

theorem mem_submodule (n : ℕ) (x : M) : x ∈ submodule R M r n ↔ ∃ y : M, r ^ n • y = x := by
  rw [submodule, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and]

def inclusion (a b : ℕ) : PowerModuleSequence.Quotient R M r a →ₗ[R] PowerModuleSequence.Quotient R M r (a + b) :=
  Submodule.mapQ _ _ (LinearMap.lsmul R M (r ^ b)) (by
    intro x hx
    obtain ⟨y, rfl⟩ := (mem_submodule R M r a x).mp hx
    apply (mem_submodule R M r (a + b) _).mpr
    refine ⟨y, ?_⟩
    change r ^ (a + b) • y = r ^ b • (r ^ a • y)
    rw [pow_add, mul_smul, smul_comm])

def projection (a b : ℕ) : PowerModuleSequence.Quotient R M r (a + b) →ₗ[R] PowerModuleSequence.Quotient R M r b :=
  Submodule.factorPow (Ideal.span {r}) M (Nat.le_add_left b a)

theorem inclusion_mk (a b : ℕ) (x : M) :
    inclusion R M r a b (Submodule.Quotient.mk x) = Submodule.Quotient.mk (r ^ b • x) := rfl

theorem projection_mk (a b : ℕ) (x : M) :
    projection R M r a b (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

theorem composition_zero (a b : ℕ) : (projection R M r a b).comp (inclusion R M r a b) = 0 := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := (submodule R M r a).mkQ_surjective q
  change (Submodule.Quotient.mk (r ^ b • x) : PowerModuleSequence.Quotient R M r b) = 0
  exact (Submodule.Quotient.mk_eq_zero (submodule R M r b)).mpr ((mem_submodule R M r b _).mpr ⟨x, rfl⟩)

theorem inclusion_injective (hr : IsSMulRegular M r) (a b : ℕ) :
    Function.Injective (inclusion R M r a b) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro q hq
  change q = 0
  obtain ⟨x, rfl⟩ := (submodule R M r a).mkQ_surjective q
  change (Submodule.Quotient.mk (r ^ b • x) : PowerModuleSequence.Quotient R M r (a + b)) = 0 at hq
  obtain ⟨y, hy⟩ := (mem_submodule R M r (a + b) _).mp ((Submodule.Quotient.mk_eq_zero (submodule R M r (a + b))).mp hq)
  have he : r ^ a • y = x := (IsSMulRegular.pow b hr) (by
    simpa only [pow_add, mul_smul, smul_comm (r ^ a) (r ^ b)] using hy)
  exact (Submodule.Quotient.mk_eq_zero (submodule R M r a)).mpr ((mem_submodule R M r a _).mpr ⟨y, he⟩)

theorem projection_surjective (a b : ℕ) : Function.Surjective (projection R M r a b) := by
  intro q
  obtain ⟨x, rfl⟩ := (submodule R M r b).mkQ_surjective q
  exact ⟨Submodule.Quotient.mk x, rfl⟩

def sequence (a b : ℕ) : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.moduleCatMk (inclusion R M r a b) (projection R M r a b) (composition_zero R M r a b)

theorem exact_sequence (a b : ℕ) : (sequence R M r a b).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro q hq
  obtain ⟨x, rfl⟩ := (submodule R M r (a + b)).mkQ_surjective q
  change (Submodule.Quotient.mk x : PowerModuleSequence.Quotient R M r b) = 0 at hq
  obtain ⟨y, hy⟩ := (mem_submodule R M r b x).mp ((Submodule.Quotient.mk_eq_zero (submodule R M r b)).mp hq)
  refine ⟨Submodule.Quotient.mk y, ?_⟩
  change (Submodule.Quotient.mk (r ^ b • y) : PowerModuleSequence.Quotient R M r (a + b)) = Submodule.Quotient.mk x
  exact congrArg Submodule.Quotient.mk hy

theorem shortExact (hr : IsSMulRegular M r) (a b : ℕ) : (sequence R M r a b).ShortExact where
  exact := exact_sequence R M r a b
  mono_f := (ModuleCat.mono_iff_injective _).mpr (inclusion_injective R M r hr a b)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (projection_surjective R M r a b)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PowerModuleSequence
