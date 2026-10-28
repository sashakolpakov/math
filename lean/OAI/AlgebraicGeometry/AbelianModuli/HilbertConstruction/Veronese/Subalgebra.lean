import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.Algebra.Operations

/-! # Subalgebra -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.Subalgebra

noncomputable section

/-! The Veronese subalgebra is the actual sum of homogeneous pieces
whose degrees are multiples of the chosen positive integer. -/
open scoped Pointwise Classical
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (g : ℕ → Submodule R A) [GradedAlgebra g] (N : ℕ)

def veroneseSubmodule : Submodule R A := ⨆ n : ℕ, g (N * n)

theorem veroneseSubmodule_mul : veroneseSubmodule g N * veroneseSubmodule g N ≤ veroneseSubmodule g N := by
  unfold veroneseSubmodule
  rw [Submodule.iSup_mul]
  apply iSup_le
  intro n
  rw [Submodule.mul_iSup]
  apply iSup_le
  intro k
  apply le_trans (show g (N * n) * g (N * k) ≤ g (N * (n + k)) from ?_) (le_iSup (fun j : ℕ => g (N * j)) (n + k))
  apply Submodule.mul_le.mpr
  intro x hx y hy
  simpa only [Nat.mul_add] using SetLike.mul_mem_graded hx hy

def veroneseSubalgebra : Subalgebra R A where
  carrier := veroneseSubmodule g N
  zero_mem' := (veroneseSubmodule g N).zero_mem
  add_mem' := (veroneseSubmodule g N).add_mem
  one_mem' := (le_iSup (fun n : ℕ => g (N * n)) 0)
    (by simpa only [Nat.mul_zero] using (SetLike.GradedOne.one_mem : (1 : A) ∈ g 0))
  mul_mem' := fun hx hy => veroneseSubmodule_mul g N (Submodule.mul_mem_mul hx hy)
  algebraMap_mem' r := (le_iSup (fun n : ℕ => g (N * n)) 0) (by
    simpa only [Nat.mul_zero, Algebra.smul_def, mul_one] using
      (g 0).smul_mem r (SetLike.GradedOne.one_mem : (1 : A) ∈ g 0))

theorem veroneseSubalgebra_toSubmodule : (veroneseSubalgebra g N).toSubmodule = veroneseSubmodule g N := rfl

theorem veronese_homogeneous_mem (n : ℕ) {a : A} (ha : a ∈ g (N * n)) : a ∈ veroneseSubalgebra g N :=
  (le_iSup (fun n : ℕ => g (N * n)) n) ha

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.Subalgebra
