import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # Adic Completion Semilinear -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionSemilinear

noncomputable section

/-! # Semilinear maps on adic completions -/

variable {R S M N : Type*} [CommRing R] [CommRing S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  (σ : R →+* S) (I : Ideal R) (J : Ideal S) (hIJ : Ideal.map σ I ≤ J)

include hIJ in
theorem preserves_powers (n : ℕ) (f : M →ₛₗ[σ] N) :
    I ^ n • (⊤ : Submodule R M) ≤ (J ^ n • (⊤ : Submodule S N)).comap f := by
  intro x hx
  refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)
  · change f (r • m) ∈ J ^ n • (⊤ : Submodule S N)
    rw [map_smulₛₗ]
    apply Submodule.smul_mem_smul _ Submodule.mem_top
    have hpow : Ideal.map σ (I ^ n) ≤ J ^ n := by
      rw [Ideal.map_pow]
      exact pow_le_pow_left' hIJ n
    exact hpow (Ideal.mem_map_of_mem σ hr)
  · change f (x + y) ∈ J ^ n • (⊤ : Submodule S N)
    rw [map_add]
    exact Submodule.add_mem _ hx hy

def reduce (f : M →ₛₗ[σ] N) (n : ℕ) :
    M ⧸ (I ^ n • (⊤ : Submodule R M)) →ₛₗ[σ]
      N ⧸ (J ^ n • (⊤ : Submodule S N)) :=
  Submodule.mapQ _ _ f (preserves_powers σ I J hIJ n f)

theorem transition_reduce (f : M →ₛₗ[σ] N) {m n : ℕ} (h : m ≤ n)
    (x : M ⧸ (I ^ n • (⊤ : Submodule R M))) :
    AdicCompletion.transitionMap J N h (reduce σ I J hIJ f n x) =
      reduce σ I J hIJ f m (AdicCompletion.transitionMap I M h x) := by
  induction x using Submodule.Quotient.induction_on with
  | H x => rfl

def map (f : M →ₛₗ[σ] N) : AdicCompletion I M →ₛₗ[σ] AdicCompletion J N where
  toFun x := ⟨fun n => reduce σ I J hIJ f n (x.val n), fun {m n} h =>
    (transition_reduce σ I J hIJ f h (x.val n)).trans
      (congrArg (reduce σ I J hIJ f m) (x.property h))⟩
  map_add' x y := by
    apply AdicCompletion.ext
    intro n
    exact map_add (reduce σ I J hIJ f n) (x.val n) (y.val n)
  map_smul' r x := by
    apply AdicCompletion.ext
    intro n
    exact map_smulₛₗ (reduce σ I J hIJ f n) r (x.val n)

theorem map_of (f : M →ₛₗ[σ] N) (x : M) :
    AdicCompletionSemilinear.map σ I J hIJ f (AdicCompletion.of I M x) = AdicCompletion.of J N (f x) := rfl

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionSemilinear
