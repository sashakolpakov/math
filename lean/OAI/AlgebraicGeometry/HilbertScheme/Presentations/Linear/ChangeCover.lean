import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.CommonCover
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.StandardPolynomialCover
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.Changes

/-! # Change Cover -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.ChangeCover.GradedHilbert

noncomputable section

/-! The linear forms of a coordinate automorphism give the same actual graded Čech exactness as the original variables. -/

open _root_.MvPolynomial DirectSum

universe u v

variable {K : Type u} [Field K] {n : ℕ}

def changedLinearCover (e : Hilbert.Polynomial.GradedHilbert.grading K n 1 ≃ₗ[K] Hilbert.Polynomial.GradedHilbert.grading K n 1) :
    Fin (n + 1) → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n := fun i => (e (Changes.GradedHilbert.linearVariable i)).val

theorem changedLinearCover_homogeneous (e : Hilbert.Polynomial.GradedHilbert.grading K n 1 ≃ₗ[K] Hilbert.Polynomial.GradedHilbert.grading K n 1) (i : Fin (n + 1)) :
    (changedLinearCover e i).IsHomogeneous 1 := (e (Changes.GradedHilbert.linearVariable i)).property

theorem changedLinearCover_span (e : Hilbert.Polynomial.GradedHilbert.grading K n 1 ≃ₗ[K] Hilbert.Polynomial.GradedHilbert.grading K n 1) :
    Submodule.span K (Set.range (changedLinearCover e)) =
      Submodule.span K (Set.range (X : Fin (n + 1) → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact changedLinearCover_homogeneous e i
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hp : (e.symm (Changes.GradedHilbert.linearVariable i)).val ∈
        Submodule.span K (Set.range (X : Fin (n + 1) → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) := by
      rw [← homogeneousSubmodule_one_eq_span_X]
      exact (e.symm (Changes.GradedHilbert.linearVariable i)).property
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hp
    have heq : ∑ j, c j • changedLinearCover e j = X i := by
      have h := congrArg (Changes.GradedHilbert.extendLinearMap e.toLinearMap) hc
      simp only [map_sum, map_smul, Changes.GradedHilbert.extendLinearMap_X, Changes.GradedHilbert.extendLinearMap_linear,
        LinearEquiv.coe_coe, e.apply_symm_apply] at h
      exact h
    rw [← heq]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))

variable (M : Type v) [AddCommGroup M] [Module K M] [Module (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) M]
  [IsScalarTower K (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) M]
variable (ℳ : ℤ → Submodule K M) [Decomposition ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := Fin (n + 1)) K) ℳ]

theorem changedLinearCover_moduleCechExactAt_iff (e : Hilbert.Polynomial.GradedHilbert.grading K n 1 ≃ₗ[K] Hilbert.Polynomial.GradedHilbert.grading K n 1)
    (d : ℤ) (q : ℕ) :
    Polynomial.CoverModule.ProjectiveCech.polynomialCoverCechExactAt K (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) M (changedLinearCover e) ℳ d q ↔
      Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := Fin (n + 1)) K M ℳ d q :=
  (Finite.CommonCover.ProjectiveCech.polynomialCover_exact_iff_of_span_eq K M ℳ (changedLinearCover e) X
    (changedLinearCover_homogeneous e) (isHomogeneous_X K) (changedLinearCover_span e) d q).trans
      (StandardPolynomialCover.ProjectiveCech.polynomialCover_X_exact_iff K M ℳ d q)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.ChangeCover.GradedHilbert
