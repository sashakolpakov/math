import OAI.Analysis.PDE.Elliptic.Boundary.InversePullback

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The vector obtained by applying a nondivergence operator to a chart.
It depends on the coefficient values and the second chart derivatives,
never on derivatives of the coefficient. -/
def chartDrift (A : E → E →L[ℝ] E) (P : E → E) (x : E) : E :=
  ∑ i, fderiv ℝ (fderiv ℝ P) x (A x (stdOrthonormalBasis ℝ E i))
    (stdOrthonormalBasis ℝ E i)

theorem ellipticTrace_linear_chart (A : E → E →L[ℝ] E) (P : E → E)
    (L : E →L[ℝ] ℝ) (x : E) (hP : ContDiffAt ℝ 2 P x) :
    ellipticTrace A (fun y => L (P y)) x = L (chartDrift A P x) := by
  let b := stdOrthonormalBasis ℝ E
  have hLP : ContDiffAt ℝ 2 (fun y => L (P y)) x := L.contDiff.contDiffAt.comp x hP
  change LinearMap.trace ℝ E ((A x).toLinearMap *
    (fderiv ℝ (gradient (fun y => L (P y))) x).toLinearMap) = _
  rw [LinearMap.trace_mul_comm, LinearMap.trace_eq_sum_inner _ b]
  simp only [chartDrift, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℝ (b i) (fderiv ℝ (gradient (fun y => L (P y))) x (A x (b i))) = _
  rw [real_inner_comm, inner_fderiv_gradient_at hLP, second_fderiv_linear_comp L hP]

theorem chartDrift_norm (A : E → E →L[ℝ] E) (P : E → E) (x : E) :
    ‖chartDrift A P x‖ ≤ Module.finrank ℝ E * ‖fderiv ℝ (fderiv ℝ P) x‖ * ‖A x‖ := by
  let b := stdOrthonormalBasis ℝ E
  apply (norm_sum_le _ _).trans
  calc
    (∑ i, ‖fderiv ℝ (fderiv ℝ P) x (A x (b i)) (b i)‖) ≤
        ∑ _i : Fin (Module.finrank ℝ E), ‖fderiv ℝ (fderiv ℝ P) x‖ * ‖A x‖ := by
      apply Finset.sum_le_sum
      intro i _
      have hn : ‖b i‖ = 1 := b.norm_eq_one i
      have hA := (A x).le_opNorm (b i)
      have hD := (fderiv ℝ (fderiv ℝ P) x).le_opNorm (A x (b i))
      have hB := (fderiv ℝ (fderiv ℝ P) x (A x (b i))).le_opNorm (b i)
      rw [hn, mul_one] at hA hB
      exact hB.trans (hD.trans (mul_le_mul_of_nonneg_left hA (norm_nonneg _)))
    _ = Module.finrank ℝ E * ‖fderiv ℝ (fderiv ℝ P) x‖ * ‖A x‖ := by simp; ring

def inverseChartDrift (A : E → E →L[ℝ] E) (G P : E → E) (y : E) : E :=
  fderiv ℝ P (G y) (chartDrift
    (fun z => pullbackEllipticOperator (fderiv ℝ P (G z)) (A (G z))) G y)

/-- The transformed nondivergence equation has a genuine first-order
drift whose coefficients involve no derivatives of the original A. -/
theorem ellipticTrace_inverse_chart_with_drift
    (A : E → E →L[ℝ] E) {G P : E → E} {u : E → ℝ} {y : E}
    (hP : DifferentiableAt ℝ P (G y)) (hG : ContDiffAt ℝ 2 G y)
    (hu : ContDiffAt ℝ 2 u (G y))
    (hinv : (fun z => P (G z)) =ᶠ[𝓝 y] id) :
    ellipticTrace (fun z => pullbackEllipticOperator (fderiv ℝ P (G z)) (A (G z)))
      (fun z => u (G z)) y = ellipticTrace A u (G y) +
        fderiv ℝ (fun z => u (G z)) y (inverseChartDrift A G P y) := by
  rw [ellipticTrace_inverse_pullback A hP hG hu hinv,
    ellipticTrace_linear_chart _ _ _ _ hG]
  congr 1
  have hd := (hu.differentiableAt (by norm_num)).hasFDerivAt.comp y
    (hG.differentiableAt (by norm_num)).hasFDerivAt
  have hde : fderiv ℝ (fun z => u (G z)) y =
      (fderiv ℝ u (G y)).comp (fderiv ℝ G y) := hd.fderiv
  rw [hde]
  simp only [ContinuousLinearMap.comp_apply, inverseChartDrift]
  have hJ := inverse_jacobian_of_local_right_inverse hP (hG.differentiableAt (by norm_num)) hinv
  have he := congrArg (fun T : E →L[ℝ] E => T (chartDrift
    (fun z => pullbackEllipticOperator (fderiv ℝ P (G z)) (A (G z))) G y)) hJ
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
    congrArg (fderiv ℝ u (G y)) he.symm

theorem inverseChartDrift_norm (A : E → E →L[ℝ] E) (G P : E → E) (y : E) :
    ‖inverseChartDrift A G P y‖ ≤
      ‖fderiv ℝ P (G y)‖ * (Module.finrank ℝ E * ‖fderiv ℝ (fderiv ℝ G) y‖ *
        ‖pullbackEllipticOperator (fderiv ℝ P (G y)) (A (G y))‖) := by
  exact ((fderiv ℝ P (G y)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (chartDrift_norm _ G y) (norm_nonneg _))

end OAI.Analysis.PDE.Elliptic
