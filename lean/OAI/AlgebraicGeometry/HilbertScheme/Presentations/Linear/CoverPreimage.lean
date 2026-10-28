import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Cover Preimage -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.CoverPreimage.ProjectiveCech

noncomputable section

/-! A member of the coefficient-linear span of a finite cover has an actual homogeneous linear polynomial preimage. -/

open _root_.MvPolynomial

universe u v w

variable {σ : Type u} [Fintype σ]
variable (R : Type v) [CommRing R] {A : Type w} [CommRing A] [Algebra R A]

theorem exists_linear_cover_preimage (a : σ → A) (x : A)
    (hx : x ∈ Submodule.span R (Set.range a)) :
    ∃ l : MvPolynomial σ R, l.IsHomogeneous 1 ∧ MvPolynomial.aeval a l = x := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hx
  refine ⟨∑ i, c i • X i, ?_, ?_⟩
  · change (∑ i, c i • X i) ∈ homogeneousSubmodule σ R 1
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (isHomogeneous_X R i)
  · simp only [map_sum, map_smul, MvPolynomial.aeval_X]
    exact hc

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.CoverPreimage.ProjectiveCech
