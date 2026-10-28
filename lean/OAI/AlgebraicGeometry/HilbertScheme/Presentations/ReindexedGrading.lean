import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Module.GradedModule

/-! # Reindexed Grading -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ReindexedGrading.GradedModules

noncomputable section

/-! Reindexing an internal grading, and shifts of integer-graded modules. -/

open DirectSum

universe u v w t

variable {R : Type u} [CommRing R] {δ : Type v} [DecidableEq δ]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable (ℳ : δ → Submodule R M) [Decomposition ℳ]

def reindexedDecompose (e : δ ≃ δ) : M ≃ₗ[R] ⨁ d, ℳ (e d) :=
  (decomposeLinearEquiv ℳ).trans (DirectSum.lequivCongrLeft R e.symm)

theorem reindexedDecompose_symm (e : δ ≃ δ) :
    (reindexedDecompose ℳ e).symm.toLinearMap = DirectSum.coeLinearMap (fun d => ℳ (e d)) := by
  apply DirectSum.linearMap_ext
  intro d
  apply LinearMap.ext
  intro m
  simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof]
  change (decomposeLinearEquiv ℳ).symm
    ((DirectSum.lequivCongrLeft R e.symm).symm (DirectSum.lof R δ (fun d => ℳ (e d)) d m)) = m.val
  have he := DirectSum.lequivCongrLeft_symm_lof (R := R) (M := fun i => ℳ i)
    (h := e.symm) (k := d) (x := m)
  exact (congrArg (decomposeLinearEquiv ℳ).symm he).trans
    (decomposeLinearEquiv_symm_lof ℳ (e d) m)

@[instance_reducible]
def reindexedGradingDecomposition (e : δ ≃ δ) : Decomposition (fun d => ℳ (e d)) :=
  Decomposition.ofLinearMap (fun d => ℳ (e d)) (reindexedDecompose ℳ e).toLinearMap
    (by
      rw [← reindexedDecompose_symm]
      apply LinearMap.ext
      intro x
      exact (reindexedDecompose ℳ e).symm_apply_apply x)
    (by
      rw [← reindexedDecompose_symm]
      apply LinearMap.ext
      intro x
      exact (reindexedDecompose ℳ e).apply_symm_apply x)

variable {A : Type t} [CommRing A] [Algebra R A] [Module A M] [IsScalarTower R A M]
variable (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
variable (ℕM : ℤ → Submodule R M) [Decomposition ℕM] [SetLike.GradedSMul 𝒜 ℕM]

def shiftedGrading (a : ℤ) : ℤ → Submodule R M := fun d => ℕM (d + a)

instance shiftedGradingDecomposition (a : ℤ) : Decomposition (shiftedGrading ℕM a) :=
  reindexedGradingDecomposition ℕM (Equiv.addRight a)

instance shiftedGradingGradedSMul (a : ℤ) : SetLike.GradedSMul 𝒜 (shiftedGrading ℕM a) where
  smul_mem := by
    intro i j r m hr hm
    have hm' : m ∈ ℕM (j + a) := hm
    have h : r • m ∈ ℕM (i + (j + a)) := SetLike.GradedSMul.smul_mem hr hm'
    simpa only [shiftedGrading, vadd_eq_add, add_assoc] using h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ReindexedGrading.GradedModules
