import OAI.Analysis.PDE.Dirichlet.Rough.FixedDomainBootstrap

noncomputable section
open Set
open scoped ContDiff
namespace OAI.Analysis.PDE.Dirichlet

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

local instance fixedSmoothFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fixedSmoothFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fixedSmoothSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fixedSmoothSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- Smoothness on one fixed closed half-patch. The finite reflected
extensions used in each induction step may be local, but the working
domain and every final differentiability assertion are unchanged. -/
theorem contDiffOn_infty_halfspace_of_mixed_tangents
    (F : NonlinearJet E → ℝ) (hF : ContDiff ℝ ∞ F)
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1)
    {O : Set E} (hO : IsOpen O) {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hi : ∀ x ∈ O, 0 < ℓ x → ContDiffAt ℝ ∞ f x)
    (ht : ∀ (N : ℕ) (v : Fin N → ℓ.ker), ContDiffOn ℝ 2
      (fun z ↦ iteratedFDeriv ℝ N (fun t : ℓ.ker ↦ f (z+(t:E))) 0 v)
      ({x | 0 ≤ ℓ x} ∩ O))
    (he : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ O), F (nonlinearTwoJet f x) = 0)
    (hell : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ O),
      fderiv ℝ F (nonlinearTwoJet f x) (0,ℓ.smulRight ℓ) ≠ 0) :
    ContDiffOn ℝ ∞ f ({x | 0 ≤ ℓ x} ∩ O) := by
  have hall : ∀ k : ℕ, ContDiffOn ℝ (k+2) f ({x | 0 ≤ ℓ x} ∩ O) := by
    intro k
    induction k with
    | zero => exact hf.contDiffOn
    | succ k ih =>
        intro x hx
        by_cases hx0 : ℓ x = 0
        · have h := contDiffWithinAt_higher_at_boundary k F (hF.of_le (by simp))
            ℓ ν hν hO hx.2 hx0 hf ih (ht (k+1)) he hell
          convert h using 1 ; norm_num [Nat.succ_eq_add_one, add_assoc]
        · have hpos : 0 < ℓ x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
          exact ((hi x hx.2 hpos).of_le (by simp)).contDiffWithinAt
  rw [contDiffOn_infty]
  intro N
  exact (hall N).of_le (by exact_mod_cast (by omega : N ≤ N+2))

end OAI.Analysis.PDE.Dirichlet
