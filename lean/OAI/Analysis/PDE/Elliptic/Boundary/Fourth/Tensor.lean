import OAI.Analysis.PDE.Nonlinear.HolderComponents
import OAI.Analysis.Normed.Function.Holder.Banach.Construct

open Set
open scoped BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Nonlinear OAI.Analysis.Normed.Function.Holder

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype I]
local instance fourthTensorFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fourthTensorFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fourthTensorSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthTensorSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthTensorThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthTensorThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthTensorFourthGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthTensorFourthSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The actual fourth derivative is represented by a Hölder field with this bound. -/
def HasFourthHolderBound (S : Set E) (α : ℝ) (u : E → ℝ) (M : ℝ) : Prop :=
  ∃ Q : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
    (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value Q x = fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) x) ∧
    ‖Q‖ ≤ M

theorem HasFourthHolderBound.mono {S : Set E} {α : ℝ} {u : E → ℝ} {M N : ℝ}
    (h : HasFourthHolderBound S α u M) (hMN : M ≤ N) : HasFourthHolderBound S α u N := by
  obtain ⟨Q,hQ,hQn⟩ := h
  exact ⟨Q,hQ,hQn.trans hMN⟩

/-- Differentiation in a fixed direction commutes with the full third
derivative of a C⁴ function. Only four derivatives are needed. -/
theorem fourth_derivative_directional_third
    (u : E → ℝ) (hu : ContDiff ℝ 4 u) (x v : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) x v =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v))) x := by
  have h₁ : ContDiff ℝ 3 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have h₂ : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ u)) := h₁.fderiv_right (by norm_num)
  have h₃ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) := h₂.fderiv_right (by norm_num)
  have he : (fun y => fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y v) =
      fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v)) := by
    funext y
    exact OAI.Analysis.PDE.Nonlinear.third_derivative_directional_hessian u (hu.of_le (by norm_num)) y v
  have hd := congrArg (fun f => fderiv ℝ f x) he
  rw [fderiv_clm_apply ((h₃.differentiable (by norm_num)) x) (differentiableAt_const v)] at hd
  have hc : fderiv ℝ (fun _ : E => v) x = 0 := (hasFDerivAt_const v x).fderiv
  rw [hc, ContinuousLinearMap.comp_zero, zero_add] at hd
  ext w a b
  have hs := ((h₂.contDiffAt (x := x)).isSymmSndFDerivAt (by norm_num)).eq v w
  have hvw := congrArg (fun L => L w a b) hd
  exact (congrArg (fun L => L a b) hs).trans hvw

theorem fourth_norm_le_of_directional_thirds
    (b : OrthonormalBasis I ℝ E) (u : E → ℝ) (hu : ContDiff ℝ 4 u)
    (x : E) (M : ℝ)
    (h : ∀ i, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (b i)))) x‖ ≤ M) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) x‖ ≤ (Fintype.card I : ℝ)*M := by
  calc
    _ ≤ ∑ i, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) x (b i)‖ :=
      OAI.Analysis.PDE.Nonlinear.clm_norm_le_sum_basis b _
    _ ≤ ∑ _i : I, M := Finset.sum_le_sum (fun i _ => by
      simpa only [fourth_derivative_directional_third u hu] using h i)
    _ = _ := by simp

theorem fourth_difference_le_of_directional_thirds
    (b : OrthonormalBasis I ℝ E) (u : E → ℝ) (hu : ContDiff ℝ 4 u)
    (x y : E) (M : ℝ)
    (h : ∀ i, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (b i)))) x-
      fderiv ℝ (fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (b i)))) y‖ ≤ M) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) x-
      fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) y‖ ≤ (Fintype.card I : ℝ)*M := by
  calc
    _ ≤ ∑ i, ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) x-
        fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) y) (b i)‖ := OAI.Analysis.PDE.Nonlinear.clm_norm_le_sum_basis b _
    _ ≤ ∑ _i : I, M := Finset.sum_le_sum (fun i _ => by
      simpa only [sub_apply, fourth_derivative_directional_third u hu] using h i)
    _ = _ := by simp

/-- Actual directional third-derivative Hölder fields reconstruct the
fourth derivative field without assuming a Hölder bound on it. -/
theorem exists_fourth_holder_of_directional_thirds
    (b : OrthonormalBasis I ℝ E) {S : Set E} {α : ℝ} (hα : 0 ≤ α)
    (u : E → ℝ) (hu : ContDiff ℝ 4 u)
    (T : I → OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (hT : ∀ i (x : S), OAI.Analysis.Normed.Function.Holder.HolderMap.value (T i) x =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (b i)))) x)
    {M : ℝ} (hM : 0 ≤ M) (hTn : ∀ i, ‖T i‖ ≤ M) :
    ∃ Q : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value Q x = fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) x) ∧
      ‖Q‖ ≤ (Fintype.card I : ℝ)*M := by
  have hn (x : S) : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) x‖ ≤
      (Fintype.card I : ℝ)*M := by
    apply fourth_norm_le_of_directional_thirds b u hu x M
    intro i
    rw [← hT i x]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le _ _).trans (hTn i)
  have hh (x y : S) :
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) x-
        fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) y‖ ≤
          ((Fintype.card I : ℝ)*M)*dist x y^α := by
    have he := fourth_difference_le_of_directional_thirds b u hu x y (M*dist x y^α) (by
      intro i
      rw [← hT i x, ← hT i y]
      exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le _ _ _).trans
        (mul_le_mul_of_nonneg_right (hTn i) (Real.rpow_nonneg dist_nonneg _)))
    simpa only [mul_assoc] using he
  have h₁ : ContDiff ℝ 3 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have h₂ : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ u)) := h₁.fderiv_right (by norm_num)
  have h₃ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) := h₂.fderiv_right (by norm_num)
  have hc : Continuous (fun x : S => fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) x) :=
    (h₃.continuous_fderiv one_ne_zero).comp continuous_subtype_val
  let Q₀ : S →ᵇ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
    BoundedContinuousFunction.ofNormedAddCommGroup _ hc ((Fintype.card I : ℝ)*M) hn
  have hN : 0 ≤ (Fintype.card I : ℝ)*M := mul_nonneg (Nat.cast_nonneg _) hM
  refine ⟨OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα Q₀ hh, fun _ => rfl, ?_⟩
  exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_ofBounded_le hα Q₀ hN hh).trans
    (max_le (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le hc hN hn) le_rfl)

/-- A separately recovered normal component completes the tangential family. -/
theorem exists_fourth_holder_of_tangential_thirds [DecidableEq I]
    (b : OrthonormalBasis I ℝ E) (k : I) {S : Set E} {α : ℝ} (hα : 0 ≤ α)
    (u : E → ℝ) (hu : ContDiff ℝ 4 u)
    (T : I → OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (Tk : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (hT : ∀ i, i ≠ k → ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value (T i) x =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (b i)))) x)
    (hTk : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value Tk x =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (b k)))) x)
    {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hTn : ∀ i, i ≠ k → ‖T i‖ ≤ M) (hTkn : ‖Tk‖ ≤ N) :
    ∃ Q : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value Q x = fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) x) ∧
      ‖Q‖ ≤ (Fintype.card I : ℝ)*(M+N) := by
  let U (i : I) := if i = k then Tk else T i
  have hU (i : I) (x : S) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (U i) x =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (b i)))) x := by
    by_cases hi : i = k
    · subst i
      simpa only [U, ite_eq_left rfl] using hTk x
    · simpa only [U, ite_eq_right hi] using hT i hi x
  have hUn (i : I) : ‖U i‖ ≤ M+N := by
    by_cases hi : i = k
    · simpa only [U, ite_eq_left hi] using hTkn.trans (le_add_of_nonneg_left hM)
    · simpa only [U, ite_eq_right hi] using (hTn i hi).trans (le_add_of_nonneg_right hN)
  exact exists_fourth_holder_of_directional_thirds b hα u hu U hU
    (add_nonneg hM hN) hUn

end OAI.Analysis.PDE.Elliptic
