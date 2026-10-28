import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.Subalgebra
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubalgebraInternalDecomposition

/-! # Grading -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.Grading

noncomputable section

/-! Regrading the Veronese algebra by dividing its homogeneous degrees
by N gives an internal grading, with no extra decomposition hypothesis. -/
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (g : ℕ → Submodule R A) [GradedAlgebra g] (N : ℕ)

def veroneseGrading (n : ℕ) : Submodule R (Subalgebra.veroneseSubalgebra g N) :=
  (g (N * n)).comap (Subalgebra.veroneseSubalgebra g N).toSubmodule.subtype

instance veroneseGradedAlgebra [NeZero N] : GradedAlgebra (veroneseGrading g N) where
  toDecomposition := by
    have h : DirectSum.IsInternal (veroneseGrading g N) := by
      convert (SubalgebraInternalDecomposition.subalgebra_internalDecomposition (Subalgebra.veroneseSubalgebra g N)
    (fun n : ℕ => g (N * n))
    (fun n => le_iSup (fun k : ℕ => g (N * k)) n)
    ((DirectSum.Decomposition.isInternal g).submodule_iSupIndep.comp
      (fun _ _ h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne N)) h))
    rfl) using 1; rfl
    exact h.chooseDecomposition
  toGradedMonoid := {
    one_mem := by
      change (1 : A) ∈ g (N * 0)
      simpa only [Nat.mul_zero] using (SetLike.GradedOne.one_mem : (1 : A) ∈ g 0)
    mul_mem := by
      intro n k x y hx hy
      change x.val * y.val ∈ g (N * (n + k))
      simpa only [Nat.mul_add] using (show x.val * y.val ∈ g (N * n + N * k) from SetLike.mul_mem_graded hx hy) }

theorem veroneseGrading_mem_iff (n : ℕ) (a : Subalgebra.veroneseSubalgebra g N) :
    a ∈ veroneseGrading g N n ↔ a.val ∈ g (N * n) := Iff.rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.Grading
