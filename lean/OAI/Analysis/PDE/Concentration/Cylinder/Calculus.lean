import OAI.Analysis.PDE.Concentration.RadialComparison

namespace OAI.Analysis.PDE.Concentration

open Set Filter Laplacian InnerProductSpace
open scoped Topology ContDiff

abbrev CylinderSpace := EuclideanSpace ℝ (Fin 3)

noncomputable def cylinderAxis (i : Fin 3) : CylinderSpace :=
  EuclideanSpace.basisFun (Fin 3) ℝ i

noncomputable def cylinderRadial (θ : ℝ) : CylinderSpace :=
  Real.cos θ • cylinderAxis 1 + Real.sin θ • cylinderAxis 2

noncomputable def cylinderAngular (θ : ℝ) : CylinderSpace :=
  -Real.sin θ • cylinderAxis 1 + Real.cos θ • cylinderAxis 2

noncomputable def cylinderPoint (t r θ : ℝ) : CylinderSpace :=
  t • cylinderAxis 0 + r • cylinderRadial θ

theorem hasDerivAt_cylinderRadial (θ : ℝ) :
    HasDerivAt cylinderRadial (cylinderAngular θ) θ := by
  exact ((Real.hasDerivAt_cos θ).smul_const _).add ((Real.hasDerivAt_sin θ).smul_const _)

theorem hasDerivAt_cylinderAngular (θ : ℝ) :
    HasDerivAt cylinderAngular (-cylinderRadial θ) θ := by
  convert (((Real.hasDerivAt_sin θ).neg).smul_const (cylinderAxis 1)).add
    ((Real.hasDerivAt_cos θ).smul_const (cylinderAxis 2)) using 1
  · rfl
  · simp [cylinderRadial, neg_smul, add_comm]

theorem hasDerivAt_cylinderPoint_time (t r θ : ℝ) :
    HasDerivAt (fun s => cylinderPoint s r θ) (cylinderAxis 0) t := by
  simpa [cylinderPoint] using ((hasDerivAt_id t).smul_const (cylinderAxis 0)).add_const (r • cylinderRadial θ)

theorem hasDerivAt_cylinderPoint_radius (t r θ : ℝ) :
    HasDerivAt (fun s => cylinderPoint t s θ) (cylinderRadial θ) r := by
  simpa [cylinderPoint] using ((hasDerivAt_id r).smul_const (cylinderRadial θ)).const_add (t • cylinderAxis 0)

theorem hasDerivAt_cylinderPoint_angle (t r θ : ℝ) :
    HasDerivAt (fun s => cylinderPoint t r s) (r • cylinderAngular θ) θ := by
  exact ((hasDerivAt_cylinderRadial θ).const_smul r).const_add _

theorem cylinderPoint_add_two_pi (t r θ : ℝ) :
    cylinderPoint t r (θ + 2 * Real.pi) = cylinderPoint t r θ := by
  simp [cylinderPoint, cylinderRadial]

theorem cylinderAngular_add_two_pi (θ : ℝ) :
    cylinderAngular (θ + 2 * Real.pi) = cylinderAngular θ := by
  simp [cylinderAngular]

theorem contDiff_cylinderPoint :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ × ℝ => cylinderPoint p.1 p.2.1 p.2.2) := by
  exact (contDiff_fst.smul contDiff_const).add
    ((contDiff_fst.comp contDiff_snd).smul
      ((((Real.contDiff_cos.comp (contDiff_snd.comp contDiff_snd)).smul contDiff_const).add
        ((Real.contDiff_sin.comp (contDiff_snd.comp contDiff_snd)).smul contDiff_const))))

section Curve
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Chain rule for a second derivative along a curve, with its acceleration
kept explicit. -/
theorem second_deriv_along_curve {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {γ v : ℝ → E} (hγ : ∀ s, HasDerivAt γ (v s) s) {s : ℝ} {a : E}
    (hv : HasDerivAt v a s) :
    deriv (deriv (fun s => f (γ s))) s =
      (fderiv ℝ (fderiv ℝ f) (γ s) (v s)) (v s) + fderiv ℝ f (γ s) a := by
  have he : deriv (fun s => f (γ s)) = fun s => fderiv ℝ f (γ s) (v s) := by
    funext t
    exact (((hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp_hasDerivAt t (hγ t)).deriv
  rw [he]
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  exact (((hdf.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt s
    (hγ s)).clm_apply hv).deriv

end Curve

theorem cylinder_second_radius {f : CylinderSpace → ℝ} (hf : ContDiff ℝ 2 f)
    (t r θ : ℝ) :
    deriv (deriv (fun s => f (cylinderPoint t s θ))) r =
      (fderiv ℝ (fderiv ℝ f) (cylinderPoint t r θ) (cylinderRadial θ)) (cylinderRadial θ) := by
  simpa using second_deriv_along_curve hf (fun s => hasDerivAt_cylinderPoint_radius t s θ)
    (hasDerivAt_const r (cylinderRadial θ))

theorem cylinder_second_time {f : CylinderSpace → ℝ} (hf : ContDiff ℝ 2 f)
    (t r θ : ℝ) :
    deriv (deriv (fun s => f (cylinderPoint s r θ))) t =
      (fderiv ℝ (fderiv ℝ f) (cylinderPoint t r θ) (cylinderAxis 0)) (cylinderAxis 0) := by
  simpa using second_deriv_along_curve hf (fun s => hasDerivAt_cylinderPoint_time s r θ)
    (hasDerivAt_const t (cylinderAxis 0))

theorem cylinder_second_angle {f : CylinderSpace → ℝ} (hf : ContDiff ℝ 2 f)
    (t r θ : ℝ) :
    deriv (deriv (fun s => f (cylinderPoint t r s))) θ =
      r ^ 2 * ((fderiv ℝ (fderiv ℝ f) (cylinderPoint t r θ) (cylinderAngular θ)) (cylinderAngular θ)) -
        r * fderiv ℝ f (cylinderPoint t r θ) (cylinderRadial θ) := by
  rw [second_deriv_along_curve hf (fun s => hasDerivAt_cylinderPoint_angle t r s)
    ((hasDerivAt_cylinderAngular θ).const_smul r)]
  simp only [map_smul, map_neg, smul_apply, smul_eq_mul]
  ring

theorem cylinder_first_radius {f : CylinderSpace → ℝ} (hf : ContDiff ℝ 2 f)
    (t r θ : ℝ) :
    deriv (fun s => f (cylinderPoint t s θ)) r =
      fderiv ℝ f (cylinderPoint t r θ) (cylinderRadial θ) := by
  exact (((hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp_hasDerivAt r
    (hasDerivAt_cylinderPoint_radius t r θ)).deriv

theorem cylinder_hessian_rotation (B : CylinderSpace →L[ℝ] CylinderSpace →L[ℝ] ℝ) (θ : ℝ) :
    B (cylinderRadial θ) (cylinderRadial θ) + B (cylinderAngular θ) (cylinderAngular θ) =
      B (cylinderAxis 1) (cylinderAxis 1) + B (cylinderAxis 2) (cylinderAxis 2) := by
  simp only [cylinderRadial, cylinderAngular, map_add, map_smul,
    add_apply, smul_apply, smul_eq_mul]
  calc
    _ = (Real.sin θ ^ 2 + Real.cos θ ^ 2) *
      (B (cylinderAxis 1) (cylinderAxis 1) + B (cylinderAxis 2) (cylinderAxis 2)) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, one_mul]

theorem cylinder_laplacian_identity {f : CylinderSpace → ℝ} (hf : ContDiff ℝ 2 f)
    (t r θ : ℝ) (hr : r ≠ 0) :
    deriv (deriv (fun s => f (cylinderPoint t s θ))) r +
      deriv (fun s => f (cylinderPoint t s θ)) r / r +
      deriv (deriv (fun s => f (cylinderPoint t r s))) θ / r ^ 2 +
      deriv (deriv (fun s => f (cylinderPoint s r θ))) t = Δ f (cylinderPoint t r θ) := by
  rw [cylinder_second_radius hf, cylinder_first_radius hf, cylinder_second_angle hf,
    cylinder_second_time hf]
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Fin.sum_univ_three]
  have he := cylinder_hessian_rotation (fderiv ℝ (fderiv ℝ f) (cylinderPoint t r θ)) θ
  dsimp [cylinderAxis] at he ⊢
  field_simp
  nlinarith [congrArg (fun x : ℝ => x * r ^ 2) he]

end OAI.Analysis.PDE.Concentration
