import OAI.LinearAlgebra.Moore.Rank.Mixed.Continuity

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix
open scoped Matrix.Norms.Elementwise

def mixedMooreContinuous (m : ℕ) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin m => Matrix (Fin m) (Fin m) (Quaternion ℝ)) ℝ :=
  ⟨mixedMoore m, continuous_mixedMoore m⟩

theorem mixedMoore_update_const {m : ℕ}
    (A P : Matrix (Fin (m + 1)) (Fin (m + 1)) (Quaternion ℝ))
    (i : Fin (m + 1)) :
    mixedMoore (m + 1) (Function.update (fun _ => A) i P) =
      mixedMoore (m + 1) (Fin.cons P (fun _ => A)) := by
  have he : (fun j => Function.update (fun _ => A) i P (Equiv.swap i 0 j)) =
      Fin.cons P (fun _ => A) := by
    funext j
    by_cases h : j = 0
    · subst j
      simp
    · have hj : Equiv.swap i 0 j ≠ i := by
        intro hj
        have he := congrArg (Equiv.swap i 0) hj
        exact h (by simpa using he)
      rw [Function.update_of_ne hj]
      cases j using Fin.cases with
      | zero => exact (h rfl).elim
      | succ j => rfl
  have h := mixedMoore_comp_perm (m + 1) (Function.update (fun _ => A) i P)
    (Equiv.swap i 0)
  rw [he] at h
  exact h.symm

/-- Differentiating the diagonal recovers the actual Moore differential,
with its precise degree normalization. -/
theorem mooreDifferential_eq_mixedMoore {m : ℕ}
    (A P : Matrix (Fin (m + 1)) (Fin (m + 1)) (Quaternion ℝ)) :
    mooreDifferential (m + 1) A P =
      (m + 1 : ℝ) * mixedMoore (m + 1) (Fin.cons P (fun _ => A)) := by
  have hline : HasDerivAt
      (fun t : ℝ => fun _ : Fin (m + 1) => A + t • P) (fun _ => P) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const P).const_add A)
  have h := (mixedMooreContinuous (m + 1)).hasFDerivAt
    (fun _ => A + (0 : ℝ) • P) |>.comp_hasDerivAt 0 hline
  have he : (mixedMooreContinuous (m + 1)).linearDeriv
      (fun _ => A + (0 : ℝ) • P) (fun _ => P) =
      (m + 1 : ℝ) * mixedMoore (m + 1) (Fin.cons P (fun _ => A)) := by
    simp only [zero_smul, add_zero, ContinuousMultilinearMap.linearDeriv_apply]
    change (∑ i, mixedMoore (m + 1) (Function.update (fun _ => A) i P)) = _
    simp only [mixedMoore_update_const, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  have hd : HasDerivAt (fun t : ℝ => mooreDet (m + 1) (A + t • P))
      ((m + 1 : ℝ) * mixedMoore (m + 1) (Fin.cons P (fun _ => A))) 0 := by
    convert h using 1
    · ext t
      exact (mixedMoore_const _ _).symm
    · exact he.symm
  have ho := hasDerivAt_mooreDet_affine A P 0
  simpa only [zero_smul, add_zero] using ho.unique hd

end OAI.LinearAlgebra.Moore
