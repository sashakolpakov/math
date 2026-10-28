import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.KernelBaseChange
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Localization Clearing -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Matrix.LocalizationClearing.Grassmannian

noncomputable section

/-! A matrix relation that vanishes after principal localization vanishes after multiplying by a power. -/

universe u v w

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {ι : Type v} {ν : Type w} [Fintype ι] [Fintype ν] [DecidableEq ν]

theorem matrix_kernel_clear_localization (s : A) [IsLocalization.Away s B]
    (Q : Matrix ι ν A) (x : ν → A)
    (h : Matrix.toLin' (Q.map (algebraMap A B)) ((algebraMap A B) ∘ x) = 0) :
    ∃ k : ℕ, Matrix.toLin' Q (s ^ k • x) = 0 := by
  classical
  have hφ (i : ι) : algebraMap A B (Q.mulVec x i) = algebraMap A B 0 := by
    rw [map_zero]
    exact (RingHom.map_mulVec (algebraMap A B) Q x i).trans (congrFun h i)
  choose k hk using fun i => IsLocalization.Away.exists_of_eq s (hφ i)
  let d := ∑ i, k i
  refine ⟨d, ?_⟩
  ext i
  change Q.mulVec (s ^ d • x) i = 0
  rw [Matrix.mulVec_smul]
  change s ^ d * Q.mulVec x i = 0
  have hi : k i ≤ d := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have he : s ^ d * Q.mulVec x i = s ^ (d - k i) * (s ^ k i * Q.mulVec x i) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hi]
  rw [he, hk i, mul_zero, mul_zero]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Matrix.LocalizationClearing.Grassmannian
