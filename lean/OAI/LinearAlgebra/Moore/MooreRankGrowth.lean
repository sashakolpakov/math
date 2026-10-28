import OAI.LinearAlgebra.Moore.MooreRankDeterminant
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

noncomputable section
namespace OAI.LinearAlgebra.Moore

open Set
open scoped MatrixOrder ComplexOrder Topology

theorem QuaternionRankLE.real_smul {m r : ℕ}
    {B : Matrix (Fin m) (Fin m) (Quaternion ℝ)} (h : QuaternionRankLE r B) (t : ℝ) :
    QuaternionRankLE r (t • B) := by
  obtain ⟨L, R, rfl⟩ := h
  exact ⟨t • L, R, (Matrix.smul_mul t L R).symm⟩

open scoped Matrix.Norms.L2Operator in
theorem exists_nonneg_scalar_upper {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    ∃ M : ℝ, 0 ≤ M ∧ (M • (1 : Matrix ι ι ℂ) - A).PosSemidef := by
  refine ⟨‖A‖, norm_nonneg _, ?_⟩
  have he : A ≤ (‖A‖ : ℝ) • (1 : Matrix ι ι ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      IsSelfAdjoint.le_algebraMap_norm_self A hA
  exact he

theorem mooreDet_le_of_psd_difference {m : ℕ}
    (A B : Matrix (Fin m) (Fin m) (Quaternion ℝ))
    (hA : (complexify A).PosSemidef)
    (hAB : (complexify (B - A)).PosSemidef) : mooreDet m A ≤ mooreDet m B := by
  have hc : IsClosed {t : ℝ | mooreDet m (A + t • 1) ≤ mooreDet m (B + t • 1)} := isClosed_le
    ((continuous_mooreDet m).comp
      (continuous_const.add (continuous_id.smul continuous_const)))
    ((continuous_mooreDet m).comp
      (continuous_const.add (continuous_id.smul continuous_const)))
  have hs : Ioi (0 : ℝ) ⊆ {t | mooreDet m (A + t • 1) ≤ mooreDet m (B + t • 1)} := by
    intro t ht
    apply mooreDet_le_of_posSemidef_difference
    · rw [complexify_add, complexify_real_smul, complexify_one]
      exact Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul ht)
    · simpa only [add_sub_add_right_eq_sub] using hAB
  have hz : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by simp
  have hh := closure_minimal hs hc hz
  simpa only [Set.mem_ofPred_eq, zero_smul, add_zero] using hh

/-- Rank at most `r` gives polynomial growth of degree at most `r` in
every positive-semidefinite direction, with an arbitrary fixed PSD base. -/
theorem mooreDet_psd_rank_growth {m r : ℕ}
    (B D : Matrix (Fin m) (Fin m) (Quaternion ℝ))
    (hB : (complexify B).PosSemidef) (hD : (complexify D).PosSemidef)
    (hr : QuaternionRankLE r B) (hrm : r ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → mooreDet m (D + t • B) ≤ C * t ^ r := by
  obtain ⟨M, hM, hBM⟩ := exists_nonneg_scalar_upper (complexify B) hB.isHermitian
  obtain ⟨a, ha, hDa⟩ := exists_nonneg_scalar_upper (complexify D) hD.isHermitian
  refine ⟨(M + a) ^ r * a ^ (m-r),
    mul_nonneg (pow_nonneg (add_nonneg hM ha) _) (pow_nonneg ha _), ?_⟩
  intro t ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have hDt : (complexify (D + t • B)).PosSemidef := by
    rw [complexify_add, complexify_real_smul]
    exact hD.add (hB.smul ht0)
  have hdiff : (complexify ((t • B + a • 1) - (D + t • B))).PosSemidef := by
    have he : (t • B + a • 1) - (D + t • B) = a • 1 - D := by abel
    rw [he, complexify_sub, complexify_real_smul, complexify_one]
    exact hDa
  have hscale : ((t * M) • (1 : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ) -
      complexify (t • B)).PosSemidef := by
    rw [complexify_real_smul, mul_smul, ← smul_sub]
    exact hBM.smul ht0
  calc
    _ ≤ mooreDet m (t • B + a • 1) := mooreDet_le_of_psd_difference _ _ hDt hdiff
    _ ≤ (t * M + a) ^ r * a ^ (m-r) :=
      mooreDet_add_scalar_le_of_rank (t • B) (by
        rw [complexify_real_smul]; exact hB.smul ht0)
        hscale (hr.real_smul t) hrm (mul_nonneg ht0 hM) ha
    _ ≤ (t * (M + a)) ^ r * a ^ (m-r) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg ha _)
      apply pow_le_pow_left₀ (add_nonneg (mul_nonneg ht0 hM) ha)
      nlinarith
    _ = _ := by rw [mul_pow]; ring

end OAI.LinearAlgebra.Moore
