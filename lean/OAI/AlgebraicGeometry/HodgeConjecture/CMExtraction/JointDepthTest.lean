import Mathlib

/-! # Joint Depth Test -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.JointDepthTest.Transport

/-! Refine a cofinal divisibility depth by one prescribed positive integer. -/

theorem exists_joint_depth {P : ℕ → Prop} (d : ℕ) (hd : 0 < d)
    (h : ∃ M : ℕ, 0 < M ∧ ∀ N : ℕ, M ∣ N → P N) :
    ∃ M : ℕ, 0 < M ∧ d ∣ M ∧ ∀ N : ℕ, M ∣ N → P N := by
  obtain ⟨M, hM, hP⟩ := h
  exact ⟨M * d, Nat.mul_pos hM hd, dvd_mul_left d M,
    fun N hN => hP N ((dvd_mul_right M d).trans hN)⟩

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.JointDepthTest.Transport
