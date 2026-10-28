import Mathlib.LinearAlgebra.Pi

/-! # Inverse Limit -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.InverseLimit.ModuleInverseLimit

noncomputable section

/-! # Compatible module sections and natural equivalences -/

universe u

variable (R : Type u) [CommRing R] (M : ℕ → Type u) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  (t : ∀ n m, n ≤ m → M m →ₗ[R] M n)

def compatible : Submodule R (∀ n, M n) where
  carrier x := ∀ n m hnm, t n m hnm (x m) = x n
  zero_mem' n m hnm := map_zero (t n m hnm)
  add_mem' hx hy n m hnm := by rw [Pi.add_apply, map_add, hx n m hnm, hy n m hnm]; rfl
  smul_mem' r _ hx n m hnm := by rw [Pi.smul_apply, map_smul, hx n m hnm]; rfl

def eval (n : ℕ) : compatible R M t →ₗ[R] M n where
  toFun x := x.val n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ext {x y : compatible R M t} (he : ∀ n, eval R M t n x = eval R M t n y) : x = y :=
  Subtype.ext (funext he)

variable (N : ℕ → Type u) [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  (s : ∀ n m, n ≤ m → N m →ₗ[R] N n)
  (f : ∀ n, M n →ₗ[R] N n) (hf : ∀ n m hnm a, f n (t n m hnm a) = s n m hnm (f m a))

def map : compatible R M t →ₗ[R] compatible R N s where
  toFun x := ⟨fun n => f n (x.val n), by
    intro n m hnm
    exact (hf n m hnm (x.val m)).symm.trans (congrArg (f n) (x.property n m hnm))⟩
  map_add' x y := ModuleInverseLimit.ext R N s (fun n => (f n).map_add (x.val n) (y.val n))
  map_smul' r x := ModuleInverseLimit.ext R N s (fun n => (f n).map_smul r (x.val n))

variable (e : ∀ n, M n ≃ₗ[R] N n)
  (he : ∀ n m hnm a, e n (t n m hnm a) = s n m hnm (e m a))

include he in
theorem inverse_naturality (n m : ℕ) (hnm : n ≤ m) (a : N m) :
    (e n).symm (s n m hnm a) = t n m hnm ((e m).symm a) := by
  apply (e n).injective
  rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]

def equiv : compatible R M t ≃ₗ[R] compatible R N s :=
  LinearEquiv.ofLinearMap
    (map R M t N s (fun n => (e n).toLinearMap) he)
    (map R N s M t (fun n => (e n).symm.toLinearMap) (inverse_naturality R M t N s e he))
    (by
      apply LinearMap.ext
      intro a
      exact ModuleInverseLimit.ext R N s (fun n => (e n).apply_symm_apply (a.val n)))
    (by
      apply LinearMap.ext
      intro a
      exact ModuleInverseLimit.ext R M t (fun n => (e n).symm_apply_apply (a.val n)))

theorem equiv_eval (n : ℕ) (a : compatible R M t) :
    eval R N s n (equiv R M t N s e he a) = e n (eval R M t n a) := rfl

theorem equiv_symm_eval (n : ℕ) (a : compatible R N s) :
    eval R M t n ((equiv R M t N s e he).symm a) = (e n).symm (eval R N s n a) := rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.InverseLimit.ModuleInverseLimit
