import OAI.Analysis.PDE.Green.Physical.Extension
import OAI.Analysis.PDE.Green.InteriorCutoff

/-! Real spatial coordinates: one ignored periodic real coordinate and two
imaginary fiber coordinates per complex fiber dimension. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory
open scoped Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

def complexSpatialProjection (c : (ι × Fin 3) ≃ Fin N) :
    (Fin N → ℝ) →L[ℝ] (ι → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    Complex.ofRealCLM.comp (ContinuousLinearMap.proj (c (i, 1))) +
      Complex.I • Complex.ofRealCLM.comp (ContinuousLinearMap.proj (c (i, 2)))

def realSpatialLift (c : (ι × Fin 3) ≃ Fin N) :
    (ι → ℂ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi fun j =>
    if (c.symm j).2 = 1 then Complex.reCLM.comp (ContinuousLinearMap.proj (c.symm j).1)
    else if (c.symm j).2 = 2 then Complex.imCLM.comp (ContinuousLinearMap.proj (c.symm j).1)
    else 0

omit [Fintype ι] [DecidableEq ι] in
theorem complexSpatialProjection_apply (c : (ι × Fin 3) ≃ Fin N) (x : Fin N → ℝ) (i : ι) :
    complexSpatialProjection c x i = (x (c (i, 1)) : ℂ) + Complex.I * x (c (i, 2)) := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem complexSpatialProjection_realSpatialLift (c : (ι × Fin 3) ≃ Fin N) (v : ι → ℂ) :
    complexSpatialProjection c (realSpatialLift c v) = v := by
  ext i
  simp [complexSpatialProjection, realSpatialLift, Complex.ext_iff]

omit [DecidableEq ι] in
theorem complexSpatialProjection_norm_le (c : (ι × Fin 3) ≃ Fin N) :
    ‖complexSpatialProjection c‖ ≤ 2 := by
  apply (complexSpatialProjection c).opNorm_le_bound (by norm_num)
  intro x
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  rw [complexSpatialProjection_apply]
  calc
    _ ≤ ‖(x (c (i, 1)) : ℂ)‖ + ‖Complex.I * x (c (i, 2))‖ := norm_add_le _ _
    _ = ‖x (c (i, 1))‖ + ‖x (c (i, 2))‖ := by simp
    _ ≤ 2 * ‖x‖ := by linarith [norm_le_pi_norm x (c (i, 1)), norm_le_pi_norm x (c (i, 2))]

omit [DecidableEq ι] in
theorem realSpatialLift_norm_le (c : (ι × Fin 3) ≃ Fin N) :
    ‖realSpatialLift c‖ ≤ 1 := by
  apply (realSpatialLift c).opNorm_le_bound (by norm_num)
  intro v
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
  intro j
  simp only [realSpatialLift, ContinuousLinearMap.pi_apply]
  split_ifs
  · exact (Complex.abs_re_le_norm _).trans (norm_le_pi_norm v _)
  · exact (Complex.abs_im_le_norm _).trans (norm_le_pi_norm v _)
  · simp

theorem sum_coordinate_derivative (L : (Fin N → ℝ) →L[ℝ] ℝ) (v : Fin N → ℝ) :
    (∑ i, L (Pi.single i 1) * v i) = L v := by
  have hv : (∑ i, v i • Pi.single i (1 : ℝ)) = v := by
    ext j
    simp [Pi.single_apply]
  calc
    _ = ∑ i, L (v i • Pi.single i (1 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [mul_comm]
    _ = L (∑ i, v i • Pi.single i (1 : ℝ)) := (map_sum L _ _).symm
    _ = L v := congrArg L hv

omit [Fintype ι] [DecidableEq ι] in
theorem complexSpatialProjection_update_real (c : (ι × Fin 3) ≃ Fin N)
    (x : Fin N → ℝ) (j : Fin N) (t : ℝ) (hj : (c.symm j).2 = 0) :
    complexSpatialProjection c (Function.update x j t) = complexSpatialProjection c x := by
  ext i
  have hn (k : Fin 3) (hk : k ≠ 0) : c (i, k) ≠ j := by
    intro he
    have h := congrArg (fun z => (c.symm z).2) he
    exact hk (by simpa [hj] using h)
  simp [complexSpatialProjection_apply, Function.update_of_ne (hn 1 (by decide)),
    Function.update_of_ne (hn 2 (by decide))]

def liftedSpatialField (c : (ι × Fin 3) ≃ Fin N) (V : (ι → ℂ) → (ι → ℂ)) :
    (Fin N → ℝ) → (Fin N → ℝ) :=
  fun x => realSpatialLift c (V (complexSpatialProjection c x))

omit [DecidableEq ι] in
theorem contDiff_liftedSpatialField (c : (ι × Fin 3) ≃ Fin N)
    {V : (ι → ℂ) → (ι → ℂ)} {k : WithTop ℕ∞} (hV : ContDiff ℝ k V) :
    ContDiff ℝ k (liftedSpatialField c V) :=
  (realSpatialLift c).contDiff.comp (hV.comp (complexSpatialProjection c).contDiff)

omit [DecidableEq ι] in
theorem liftedSpatialField_fderiv (c : (ι × Fin 3) ≃ Fin N)
    {V : (ι → ℂ) → (ι → ℂ)} (x : Fin N → ℝ)
    (hV : DifferentiableAt ℝ V (complexSpatialProjection c x)) :
    fderiv ℝ (liftedSpatialField c V) x = (realSpatialLift c).comp
      ((fderiv ℝ V (complexSpatialProjection c x)).comp (complexSpatialProjection c)) :=
  ((realSpatialLift c).hasFDerivAt.comp x
    (hV.hasFDerivAt.comp x (complexSpatialProjection c).hasFDerivAt)).fderiv

omit [DecidableEq ι] in
theorem liftedSpatialField_derivative_norm_le (c : (ι × Fin 3) ≃ Fin N)
    {V : (ι → ℂ) → (ι → ℂ)} (x : Fin N → ℝ)
    (hV : DifferentiableAt ℝ V (complexSpatialProjection c x))
    {C : ℝ} (hC : ‖fderiv ℝ V (complexSpatialProjection c x)‖ ≤ C) :
    ‖fderiv ℝ (liftedSpatialField c V) x‖ ≤ 2 * C := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hC
  rw [liftedSpatialField_fderiv c x hV]
  calc
    _ ≤ ‖realSpatialLift c‖ *
        (‖fderiv ℝ V (complexSpatialProjection c x)‖ * ‖complexSpatialProjection c‖) :=
      ((realSpatialLift c).opNorm_comp_le _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (C * 2) := by
      gcongr
      · exact realSpatialLift_norm_le c
      · exact complexSpatialProjection_norm_le c
    _ = 2 * C := by ring

omit [DecidableEq ι] in
theorem liftedSpatialField_transverse (c : (ι × Fin 3) ≃ Fin N)
    {R : (ι → ℂ) → ℝ} (V : (ι → ℂ) → (ι → ℂ)) (x : Fin N → ℝ)
    (hR : DifferentiableAt ℝ R (complexSpatialProjection c x)) :
    (∑ i, fderiv ℝ (R ∘ complexSpatialProjection c) x (Pi.single i 1) *
      liftedSpatialField c V x i) =
      fderiv ℝ R (complexSpatialProjection c x) (V (complexSpatialProjection c x)) := by
  rw [sum_coordinate_derivative,
    (hR.hasFDerivAt.comp x (complexSpatialProjection c).hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.comp_apply, liftedSpatialField,
    complexSpatialProjection_realSpatialLift]

theorem vectorField_divergence_norm_le {W : (Fin N → ℝ) → (Fin N → ℝ)}
    {x : Fin N → ℝ} (hW : DifferentiableAt ℝ W x)
    {C : ℝ} (hC : ‖fderiv ℝ W x‖ ≤ C) :
    ‖∑ i, fderiv ℝ (fun y => W y i) x (Pi.single i 1)‖ ≤ (N : ℝ) * C := by
  calc
    _ ≤ ∑ i, ‖fderiv ℝ (fun y => W y i) x (Pi.single i 1)‖ :=
      norm_sum_le Finset.univ (fun i : Fin N =>
        (fderiv ℝ (fun y => W y i) x) (Pi.single i (1 : ℝ)))
    _ ≤ ∑ _i : Fin N, C := by
      apply Finset.sum_le_sum
      intro i _
      have hi := (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp x hW.hasFDerivAt
      change ‖fderiv ℝ ((ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ) ∘ W) x
        (Pi.single i 1)‖ ≤ C
      rw [hi.fderiv]
      change ‖(fderiv ℝ W x (Pi.single i 1)) i‖ ≤ C
      have hsingle : ‖(Pi.single i (1 : ℝ) : Fin N → ℝ)‖ ≤ 1 := by
        apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
        intro j
        by_cases hj : i = j <;> simp [hj]
      calc
        _ ≤ ‖fderiv ℝ W x (Pi.single i 1)‖ := norm_le_pi_norm _ _
        _ ≤ ‖fderiv ℝ W x‖ * ‖(Pi.single i (1 : ℝ) : Fin N → ℝ)‖ :=
          (fderiv ℝ W x).le_opNorm _
        _ ≤ ‖fderiv ℝ W x‖ * 1 := by
          exact mul_le_mul_of_nonneg_left hsingle (norm_nonneg _)
        _ ≤ C := by simpa only [mul_one] using hC
    _ = (N : ℝ) * C := by simp

omit [DecidableEq ι] in
theorem abs_coordinate_le_complexProjection_norm (c : (ι × Fin 3) ≃ Fin N)
    (x : Fin N → ℝ) (j : Fin N) (hj : (c.symm j).2 ≠ 0) :
    ‖x j‖ ≤ ‖complexSpatialProjection c x‖ := by
  rcases c.surjective j with ⟨⟨i, k⟩, rfl⟩
  simp only [Equiv.symm_apply_apply] at hj
  fin_cases k
  · exact False.elim (hj rfl)
  · have h := Complex.abs_re_le_norm (complexSpatialProjection c x i)
    simp only [complexSpatialProjection_apply, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul,
      mul_zero, sub_zero, add_zero] at h
    exact h.trans (norm_le_pi_norm (complexSpatialProjection c x) i)
  · have h := Complex.abs_im_le_norm (complexSpatialProjection c x i)
    simp only [complexSpatialProjection_apply, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul,
      one_mul, zero_add] at h
    exact h.trans (norm_le_pi_norm (complexSpatialProjection c x) i)

omit [Fintype ι] [DecidableEq ι] in
theorem liftedSpatialField_zero_real (c : (ι × Fin 3) ≃ Fin N)
    (V : (ι → ℂ) → (ι → ℂ)) (x : Fin N → ℝ) (j : Fin N)
    (hj : (c.symm j).2 = 0) : liftedSpatialField c V x j = 0 := by
  simp [liftedSpatialField, realSpatialLift, hj]

end OAI.Analysis.PDE.Green
