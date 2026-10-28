import OAI.LinearAlgebra.Moore.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

noncomputable section
namespace OAI.LinearAlgebra.Moore

/-- The factorization characterization of quaternion rank at most `r`.
This uses genuine quaternion matrix multiplication (and thus the usual right
column rank), rather than applying a commutative-field rank to quaternion entries. -/
def QuaternionRankLE {m : ℕ} (r : ℕ)
    (B : Matrix (Fin m) (Fin m) (Quaternion ℝ)) : Prop :=
  ∃ L : Matrix (Fin m) (Fin r) (Quaternion ℝ),
    ∃ R : Matrix (Fin r) (Fin m) (Quaternion ℝ), B = L * R

theorem QuaternionRankLE.complexify_rank_le {m r : ℕ}
    {B : Matrix (Fin m) (Fin m) (Quaternion ℝ)} (h : QuaternionRankLE r B) :
    (complexify B).rank ≤ 2 * r := by
  obtain ⟨L, R, rfl⟩ := h
  rw [complexify_mul]
  exact (Matrix.rank_mul_le_left _ _).trans (by
    simpa [Nat.mul_comm] using (complexify L).rank_le_card_width)

theorem quaternionRankLE_zero {m r : ℕ} :
    QuaternionRankLE r (0 : Matrix (Fin m) (Fin m) (Quaternion ℝ)) := by
  exact ⟨0, 0, by simp⟩

theorem quaternionRankLE_self {m : ℕ}
    (B : Matrix (Fin m) (Fin m) (Quaternion ℝ)) : QuaternionRankLE m B := by
  exact ⟨B, 1, by simp⟩

end OAI.LinearAlgebra.Moore
