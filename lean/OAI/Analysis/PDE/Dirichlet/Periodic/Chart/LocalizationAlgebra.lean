import OAI.Analysis.PDE.Nonlinear.CutoffJet
import OAI.Analysis.PDE.Elliptic.Boundary.Schauder.Hessian

open Set
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance localizationFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance localizationFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance localizationSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance localizationSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The values and two genuine derivatives, with a common Hölder bound
on a specified set. This predicate imposes nothing off that set. -/
structure C2JetHolderBoundsOn (u : E → ℝ) (S : Set E) (α N : ℝ) : Prop where
  value : ∀ x ∈ S, ‖u x‖ ≤ N
  first : ∀ x ∈ S, ‖fderiv ℝ u x‖ ≤ N
  second : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ N
  value_sub : ∀ x ∈ S, ∀ y ∈ S, ‖u x-u y‖ ≤ N*‖x-y‖^α
  first_sub : ∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ u x-fderiv ℝ u y‖ ≤ N*‖x-y‖^α
  second_sub : ∀ x ∈ S, ∀ y ∈ S,
    ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ N*‖x-y‖^α

theorem localization_norm_smul_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a b : ℝ) (v w : F) :
    ‖a • v-b • w‖ ≤ ‖a‖*‖v-w‖ + ‖a-b‖*‖w‖ := by
  have he : a • v-b • w = a • (v-w)+(a-b) • w := by module
  rw [he]
  simpa only [norm_smul] using norm_add_le (a • (v-w)) ((a-b) • w)

theorem localization_norm_smulRight_sub (a b v w : E →L[ℝ] ℝ) :
    ‖a.smulRight v-b.smulRight w‖ ≤ ‖a‖*‖v-w‖ + ‖a-b‖*‖w‖ := by
  have he : a.smulRight v-b.smulRight w = a.smulRight (v-w)+(a-b).smulRight w := by
    ext x y
    simp only [add_apply, sub_apply, ContinuousLinearMap.smulRight_apply,
      smul_apply, smul_eq_mul]
    ring
  rw [he]
  simpa only [ContinuousLinearMap.norm_smulRight_apply] using
    norm_add_le (a.smulRight (v-w)) ((a-b).smulRight w)

theorem cutoff_hessian_bounds_on
    (η u : E → ℝ) (hη : ContDiff ℝ 2 η) (hu : ContDiff ℝ 2 u)
    {S : Set E} {α A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hηb : C2JetHolderBoundsOn η S α A) (hub : C2JetHolderBoundsOn u S α B) :
    (∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (fun y ↦ η y*u y)) x‖ ≤ 4*A*B) ∧
    (∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ (fderiv ℝ (fun y ↦ η y*u y)) x-
        fderiv ℝ (fderiv ℝ (fun y ↦ η y*u y)) y‖ ≤ 8*A*B*‖x-y‖^α) := by
  let F₁ x := η x • fderiv ℝ (fderiv ℝ u) x
  let F₂ x := u x • fderiv ℝ (fderiv ℝ η) x
  let F₃ x := (fderiv ℝ η x).smulRight (fderiv ℝ u x)
  let F₄ x := (fderiv ℝ u x).smulRight (fderiv ℝ η x)
  have he x : fderiv ℝ (fderiv ℝ (fun y ↦ η y*u y)) x =
      F₁ x + (F₂ x+F₃ x+F₄ x) :=
    OAI.Analysis.PDE.Nonlinear.cutoff_hessian η u hη hu x
  have hnorm x (hx : x ∈ S) :
      ‖F₁ x‖ ≤ A*B ∧ ‖F₂ x‖ ≤ A*B ∧ ‖F₃ x‖ ≤ A*B ∧ ‖F₄ x‖ ≤ A*B := by
    dsimp [F₁,F₂,F₃,F₄]
    simp only [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
    refine ⟨mul_le_mul (hηb.value x hx) (hub.second x hx) (norm_nonneg _) hA,
      ?_,mul_le_mul (hηb.first x hx) (hub.first x hx) (norm_nonneg _) hA,?_⟩
    · exact (mul_le_mul (hub.value x hx) (hηb.second x hx) (norm_nonneg _) hB).trans_eq (mul_comm B A)
    · exact (mul_le_mul (hub.first x hx) (hηb.first x hx) (norm_nonneg _) hB).trans_eq (mul_comm B A)
  have hdiff x (hx : x ∈ S) y (hy : y ∈ S) :
      ‖F₁ x-F₁ y‖ ≤ 2*A*B*‖x-y‖^α ∧ ‖F₂ x-F₂ y‖ ≤ 2*A*B*‖x-y‖^α ∧
      ‖F₃ x-F₃ y‖ ≤ 2*A*B*‖x-y‖^α ∧ ‖F₄ x-F₄ y‖ ≤ 2*A*B*‖x-y‖^α := by
    have hd : 0 ≤ ‖x-y‖^α := Real.rpow_nonneg (norm_nonneg _) _
    refine ⟨?_,?_,?_,?_⟩
    · dsimp only [F₁]
      apply (localization_norm_smul_sub _ _ _ _).trans
      have h1 := mul_le_mul (hηb.value x hx) (hub.second_sub x hx y hy) (norm_nonneg _) hA
      have h2 := mul_le_mul (hηb.value_sub x hx y hy) (hub.second y hy) (norm_nonneg _) (mul_nonneg hA hd)
      nlinarith
    · dsimp only [F₂]
      apply (localization_norm_smul_sub _ _ _ _).trans
      have h1 := mul_le_mul (hub.value x hx) (hηb.second_sub x hx y hy) (norm_nonneg _) hB
      have h2 := mul_le_mul (hub.value_sub x hx y hy) (hηb.second y hy) (norm_nonneg _) (mul_nonneg hB hd)
      nlinarith
    · apply (localization_norm_smulRight_sub _ _ _ _).trans
      have h1 := mul_le_mul (hηb.first x hx) (hub.first_sub x hx y hy) (norm_nonneg _) hA
      have h2 := mul_le_mul (hηb.first_sub x hx y hy) (hub.first y hy) (norm_nonneg _) (mul_nonneg hA hd)
      nlinarith
    · apply (localization_norm_smulRight_sub _ _ _ _).trans
      have h1 := mul_le_mul (hub.first x hx) (hηb.first_sub x hx y hy) (norm_nonneg _) hB
      have h2 := mul_le_mul (hub.first_sub x hx y hy) (hηb.first y hy) (norm_nonneg _) (mul_nonneg hB hd)
      nlinarith
  constructor
  · intro x hx
    rw [he]
    have hn := hnorm x hx
    have ht := norm_add_le (F₁ x) (F₂ x+F₃ x+F₄ x)
    have ht' := norm_add_le (F₂ x+F₃ x) (F₄ x)
    have ht'' := norm_add_le (F₂ x) (F₃ x)
    linarith
  · intro x hx y hy
    rw [he,he]
    have hid : F₁ x+(F₂ x+F₃ x+F₄ x)-(F₁ y+(F₂ y+F₃ y+F₄ y)) =
        (F₁ x-F₁ y)+((F₂ x-F₂ y)+(F₃ x-F₃ y)+(F₄ x-F₄ y)) := by abel
    rw [hid]
    have hn := hdiff x hx y hy
    have ht := norm_add_le (F₁ x-F₁ y) ((F₂ x-F₂ y)+(F₃ x-F₃ y)+(F₄ x-F₄ y))
    have ht' := norm_add_le ((F₂ x-F₂ y)+(F₃ x-F₃ y)) (F₄ x-F₄ y)
    have ht'' := norm_add_le (F₂ x-F₂ y) (F₃ x-F₃ y)
    linarith

end OAI.Analysis.PDE.Dirichlet
