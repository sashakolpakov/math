import OAI.NumberTheory.PadicHodge.IntegralComparison.SequentialModuleDifference

/-! # Compatible Sequence Equivalence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CompatibleSequenceEquivalence

noncomputable section

/-! Componentwise linear equivalences commuting with transitions identify compatible inverse sequences. -/

universe u v w

variable (R : Type u) [Ring R] (M : ℕ → Type v) (N : ℕ → Type w)
  [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  (s : ∀ n, M (n + 1) →ₗ[R] M n) (t : ∀ n, N (n + 1) →ₗ[R] N n)
  (e : ∀ n, M n ≃ₗ[R] N n)
  (he : ∀ n x, e n (s n x) = t n (e (n + 1) x))

include he in
theorem compatible (x : ∀ n, M n) :
    SequentialModuleDifference.difference R M s x = 0 ↔
      SequentialModuleDifference.difference R N t (fun n => e n (x n)) = 0 := by
  rw [SequentialModuleDifference.difference_eq_zero_iff,
    SequentialModuleDifference.difference_eq_zero_iff]
  constructor
  · intro h n
    exact (he n (x (n + 1))).symm.trans (congrArg (e n) (h n))
  · intro h n
    exact (e n).injective ((he n (x (n + 1))).trans (h n))

def equivalence : LinearMap.ker (SequentialModuleDifference.difference R M s) ≃ₗ[R]
    LinearMap.ker (SequentialModuleDifference.difference R N t) where
  toFun x := ⟨fun n => e n (x.val n), (compatible R M N s t e he x.val).mp x.property⟩
  invFun y := ⟨fun n => (e n).symm (y.val n),
    (compatible R M N s t e he (fun n => (e n).symm (y.val n))).mpr (by
      simpa only [LinearEquiv.apply_symm_apply, LinearMap.mem_ker] using y.property)⟩
  left_inv x := by
    apply Subtype.ext
    funext n
    exact (e n).symm_apply_apply (x.val n)
  right_inv y := by
    apply Subtype.ext
    funext n
    exact (e n).apply_symm_apply (y.val n)
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact (e n).map_add (x.val n) (y.val n)
  map_smul' r x := by
    apply Subtype.ext
    funext n
    exact (e n).map_smul r (x.val n)

theorem equivalence_apply (x : LinearMap.ker (SequentialModuleDifference.difference R M s)) (n : ℕ) :
    (equivalence R M N s t e he x).val n = e n (x.val n) := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CompatibleSequenceEquivalence
