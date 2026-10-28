import OAI.Analysis.Calculus.Current.Operations

namespace OAI.Analysis.Calculus.Current

noncomputable section

def pairedC {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (z : Index d → ℂ) (a b : Index d) : ℂ :=
  (tangentField v z a * star (tangentField v' z b) +
    tangentField v' z a * star (tangentField v z b)) * (gaussianField κ κ' v v' z : ℂ)

def pairedE {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (z : Index d → ℂ) (a b : Index d) : ℂ :=
  (tangentField v z a * tangentField v' z b -
    tangentField v' z a * tangentField v z b) *
      (gaussianField κ κ' v v' z : ℂ) * movingUnit z

def crossPhase {d : ℕ} (κ' : ℝ) (v' : Fin d → ℝ) (V : Index d → ℂ) : ℂ :=
  (κ' : ℂ) * ∑ a, phaseRow (fun i => (v' i : ℂ)) a * V a

theorem differentiableAt_pairedC {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (z : Index d → ℂ) (hY : z none ≠ 0) (a b : Index d) :
    DifferentiableAt ℝ (fun w => pairedC κ κ' v v' w a b) z := by
  have hv := differentiableAt_tangentField v z hY
  have hv' := differentiableAt_tangentField v' z hY
  exact (((hv a).fun_mul (hv' b).star).fun_add ((hv' a).fun_mul (hv b).star)).fun_mul
    (differentiableAt_gaussianField_complex κ κ' v v' z hY)

theorem differentiableAt_pairedE {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (z : Index d → ℂ) (hY : z none ≠ 0) (a b : Index d) :
    DifferentiableAt ℝ (fun w => pairedE κ κ' v v' w a b) z := by
  have hv := differentiableAt_tangentField v z hY
  have hv' := differentiableAt_tangentField v' z hY
  exact ((((hv a).fun_mul (hv' b)).fun_sub ((hv' a).fun_mul (hv b))).fun_mul
    (differentiableAt_gaussianField_complex κ κ' v v' z hY)).fun_mul
      (differentiableAt_movingUnit z hY)

theorem moving_antisymmetric_derivative {d : ℕ} (v v' : Fin d → ℝ)
    (z : Index d → ℂ) (hY : z none ≠ 0) (b : Index d) :
    complexBarDirectional (fun w => star (tangentField v' w b) * star (movingUnit w))
        z (tangentField v z) =
      complexBarDirectional (fun w => star (tangentField v w b) * star (movingUnit w))
        z (tangentField v' z) := by
  have he := (differentiableAt_movingUnit z hY).star
  rw [complexBarDirectional_mul _ _ z _ ((differentiableAt_tangentField v' z hY b).star) he,
    complexBarDirectional_mul _ _ z _ ((differentiableAt_tangentField v z hY b).star) he,
    complexBarDirectional_conjugate_movingUnit z _ hY,
    complexBarDirectional_conjugate_movingUnit z _ hY]
  have ht : tangentField v z none = 1 := rfl
  have ht' : tangentField v' z none = 1 := rfl
  rw [ht, ht', star_one]
  have hc := current_final_cancellation v v' z hY b
  linear_combination hc

/-- The complex part of every paired current has the exact required
antiholomorphic divergence. -/
theorem pairedC_imaginary_divergence {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (z : Index d → ℂ) (hY : z none ≠ 0) (b : Index d) :
    (∑ a, barD (fun w => star (pairedC κ κ' v v' w a b)) z a) =
      (gaussianField κ κ' v v' z : ℂ) * movingUnit z *
        (crossPhase κ' v' (tangentField v z) * tangentField v' z b +
          crossPhase κ v (tangentField v' z) * tangentField v z b) := by
  have hg := differentiableAt_gaussianField_complex κ κ' v v' z hY
  have hv := differentiableAt_tangentField v z hY
  have hv' := differentiableAt_tangentField v' z hY
  have hform (a : Index d) : (fun w => star (pairedC κ κ' v v' w a b)) =
      (fun w => (star (tangentField v w a) * (gaussianField κ κ' v v' w : ℂ)) *
          tangentField v' w b +
        (star (tangentField v' w a) * (gaussianField κ κ' v v' w : ℂ)) *
          tangentField v w b) := by
    funext w
    simp only [pairedC, star_mul, star_add, Complex.star_def, Complex.conj_ofReal,
      Complex.conj_conj]
    ring
  simp_rw [hform, barD_add _ _ z (((hv _).star.fun_mul hg).fun_mul (hv' b))
    (((hv' _).star.fun_mul hg).fun_mul (hv b))]
  rw [Finset.sum_add_distrib]
  have h1 := weighted_tangentField_product_divergence κ κ' v v'
    (fun w => tangentField v' w b) z hY (hv' b)
  have h2 := weighted_tangentField_product_divergence κ' κ v' v
    (fun w => tangentField v w b) z hY (hv b)
  rw [← gaussianField_swap κ κ' v v'] at h2
  rw [h1, h2, complexBarDirectional_holomorphic _ z _
    (differentiableAt_tangentField_complex v' z hY b),
    complexBarDirectional_holomorphic _ z _ (differentiableAt_tangentField_complex v z hY b)]
  unfold crossPhase
  ring

/-- The skew part's divergence includes and cancels the differentiated moving
embedding, proving the genuinely off-diagonal Gaussian identity. -/
theorem pairedE_imaginary_divergence {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (z : Index d → ℂ) (hY : z none ≠ 0) (b : Index d) :
    (∑ a, barD (fun w => star (pairedE κ κ' v v' w a b)) z a) =
      (gaussianField κ κ' v v' z : ℂ) *
        (crossPhase κ' v' (tangentField v z) * star (tangentField v' z b) -
          crossPhase κ v (tangentField v' z) * star (tangentField v z b)) := by
  have hg := differentiableAt_gaussianField_complex κ κ' v v' z hY
  have hv := differentiableAt_tangentField v z hY
  have hv' := differentiableAt_tangentField v' z hY
  have he := (differentiableAt_movingUnit z hY).star
  have hform (a : Index d) : (fun w => star (pairedE κ κ' v v' w a b)) =
      (fun w => (star (tangentField v w a) * (gaussianField κ κ' v v' w : ℂ)) *
          (star (tangentField v' w b) * star (movingUnit w)) -
        (star (tangentField v' w a) * (gaussianField κ κ' v v' w : ℂ)) *
          (star (tangentField v w b) * star (movingUnit w))) := by
    funext w
    simp only [pairedE, star_mul, star_sub, Complex.star_def, Complex.conj_ofReal]
    ring
  simp_rw [hform, barD_sub _ _ z
    (((hv _).star.fun_mul hg).fun_mul ((hv' b).star.fun_mul he))
    (((hv' _).star.fun_mul hg).fun_mul ((hv b).star.fun_mul he))]
  rw [Finset.sum_sub_distrib]
  have h1 := weighted_tangentField_product_divergence κ κ' v v'
    (fun w => star (tangentField v' w b) * star (movingUnit w)) z hY ((hv' b).star.fun_mul he)
  have h2 := weighted_tangentField_product_divergence κ' κ v' v
    (fun w => star (tangentField v w b) * star (movingUnit w)) z hY ((hv b).star.fun_mul he)
  rw [← gaussianField_swap κ κ' v v'] at h2
  rw [h1, h2, moving_antisymmetric_derivative v v' z hY b]
  have hu := movingUnit_mul_star z hY
  unfold crossPhase
  linear_combination (gaussianField κ κ' v v' z : ℂ) *
    ((κ' : ℂ) * (∑ a, phaseRow (fun i => (v' i : ℂ)) a * tangentField v z a) *
      star (tangentField v' z b) - (κ : ℂ) *
        (∑ a, phaseRow (fun i => (v i : ℂ)) a * tangentField v' z a) *
          star (tangentField v z b)) * hu

end
end OAI.Analysis.Calculus.Current
