import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.InverseDifference

/-! # Compatible Lifting -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CompatibleLifting

noncomputable section

/-! Finite kernels allow compatible inverse sequences to be lifted through levelwise linear maps. -/

universe u v w

variable (R : Type u) [Ring R] (M : ℕ → Type v) (N : ℕ → Type w)
  [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  (s : ∀ n, M (n + 1) →ₗ[R] M n) (t : ∀ n, N (n + 1) →ₗ[R] N n)
  (f : ∀ n, M n →ₗ[R] N n)
  (hf : ∀ n x, f n (s n x) = t n (f (n + 1) x))

def kernelTransition (n : ℕ) : LinearMap.ker (f (n + 1)) →ₗ[R] LinearMap.ker (f n) where
  toFun x := ⟨s n x.val, (hf n x.val).trans (by
    have hx : f (n + 1) x.val = 0 := x.property
    rw [hx, map_zero])⟩
  map_add' x y := Subtype.ext ((s n).map_add x.val y.val)
  map_smul' r x := Subtype.ext ((s n).map_smul r x.val)

include hf in
theorem exists_lift [∀ n, Finite (LinearMap.ker (f n))]
    (y : ∀ n, N n) (hy : ∀ n, t n (y (n + 1)) = y n)
    (hlift : ∀ n, ∃ x : M n, f n x = y n) :
    ∃ x : ∀ n, M n, (∀ n, s n (x (n + 1)) = x n) ∧ ∀ n, f n (x n) = y n := by
  classical
  choose x hx using hlift
  let d (n : ℕ) : LinearMap.ker (f n) := ⟨x n - s n (x (n + 1)), by
    change f n (x n - s n (x (n + 1))) = 0
    rw [map_sub, hf, hx, hx, hy, sub_self]⟩
  obtain ⟨z, hz⟩ := InverseDifference.surjective R (fun n => LinearMap.ker (f n))
    (kernelTransition R M N s t f hf) d
  refine ⟨fun n => x n - (z n).val, ?_, ?_⟩
  · intro n
    have h : (z n).val - s n (z (n + 1)).val = x n - s n (x (n + 1)) :=
      congrArg Subtype.val (congrFun hz n)
    rw [map_sub]
    calc
      s n (x (n + 1)) - s n (z (n + 1)).val =
          x n - (x n - s n (x (n + 1))) - s n (z (n + 1)).val := by abel
      _ = x n - ((z n).val - s n (z (n + 1)).val) - s n (z (n + 1)).val := by rw [h]
      _ = x n - (z n).val := by abel
  · intro n
    have hz' : f n (z n).val = 0 := (z n).property
    rw [map_sub, hx, hz', sub_zero]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CompatibleLifting
