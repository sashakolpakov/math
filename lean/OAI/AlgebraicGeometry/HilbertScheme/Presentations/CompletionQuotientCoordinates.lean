import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # Completion Quotient Coordinates -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.CompletionQuotientCoordinates

noncomputable section

/-! Quotient coordinates of a completion along a finitely generated ideal. -/

universe u
variable {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
include hI

theorem completion_eval_kernel (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I.map (algebraMap R (AdicCompletion I R))) ^ n := by
  ext x
  trans x ∈ (AdicCompletion.eval I R n).ker
  · have he : I ^ n • (⊤ : Ideal R) = I ^ n := by simp
    have h : Function.Injective (Ideal.Quotient.factor he.le) := by
      simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
        using Ideal.map_mk_eq_bot_of_le he.symm.le
    change AdicCompletion.evalₐ I n x = 0 ↔ AdicCompletion.eval I R n x = 0
    rw [← AdicCompletion.factor_eval_eq_evalₐ I x he.le]
    exact map_eq_zero_iff (Ideal.Quotient.factor he.le) h
  · simp [← AdicCompletion.pow_smul_top_eq_ker_eval hI, ← Ideal.map_pow]

theorem completion_quotient_base_surjective (n : ℕ) :
    Function.Surjective ((Ideal.Quotient.mk
      ((I.map (algebraMap R (AdicCompletion I R))) ^ n)).comp
        (algebraMap R (AdicCompletion I R))) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  refine ⟨r, ?_⟩
  apply Ideal.Quotient.eq.mpr
  rw [← completion_eval_kernel I hI n]
  change AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) r - x) = 0
  rw [map_sub, sub_eq_zero]
  exact hr

theorem completion_residue_base_surjective :
    Function.Surjective ((Ideal.Quotient.mk
      (I.map (algebraMap R (AdicCompletion I R)))).comp
        (algebraMap R (AdicCompletion I R))) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ I x)
  refine ⟨r, ?_⟩
  apply Ideal.Quotient.eq.mpr
  rw [← AdicCompletion.ker_evalOneₐ_eq_map I hI]
  change AdicCompletion.evalOneₐ I (algebraMap R (AdicCompletion I R) r - x) = 0
  rw [map_sub, sub_eq_zero]
  exact hr

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.CompletionQuotientCoordinates
