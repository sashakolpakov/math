import OAI.Analysis.Calculus.Current.Smooth

namespace OAI.Analysis.Calculus.Quaternion

noncomputable section
open scoped Topology

/-- The genuine second derivative of a squared norm after composition. -/
theorem hessian_norm_sq_comp {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x) (v w : E) :
    (fderiv ℝ (fderiv ℝ (fun y => ‖f y‖ ^ 2)) x v) w =
      2 * (inner ℝ (f x) ((fderiv ℝ (fderiv ℝ f) x v) w) +
        inner ℝ (fderiv ℝ f x v) (fderiv ℝ f x w)) := by
  have hf₁ := hf.differentiableAt (by norm_num)
  have hf₂ := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hu := hf.norm_sq ℝ
  have hu₂ := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : (fun y => fderiv ℝ (fun q => ‖f q‖ ^ 2) y w) =ᶠ[𝓝 x]
      (fun y => 2 * inner ℝ (f y) (fderiv ℝ f y w)) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    rw [(hy.differentiableAt (by norm_num)).hasFDerivAt.norm_sq.fderiv]
    simp
  have hleft := congrArg (fun L : E →L[ℝ] ℝ => L v) heq.fderiv_eq
  rw [fderiv_clm_apply hu₂ (differentiableAt_const w)] at hleft
  have hfw := hf₂.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have hr := (hf₁.hasFDerivAt.inner ℝ hfw).const_mul (2 : ℝ)
  rw [hr.fderiv] at hleft
  simpa [fderivInnerCLM] using hleft

/-- Scalar restriction preserves both actual derivatives of a holomorphic map. -/
theorem hessian_norm_sq_holomorphic {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {x : E} (hf : ContDiffAt ℂ 2 f x) (v w : E) :
    (fderiv ℝ (fderiv ℝ (fun y => ‖f y‖ ^ 2)) x v) w =
      2 * (inner ℝ (f x) ((fderiv ℂ (fderiv ℂ f) x v) w) +
        inner ℝ (fderiv ℂ f x v) (fderiv ℂ f x w)) := by
  rw [hessian_norm_sq_comp (hf.restrict_scalars ℝ)]
  have hD := ((hf.differentiableAt (by norm_num)).hasFDerivAt.restrictScalars ℝ).fderiv
  have hH := congrArg (fun L => L ![v, w])
    (hf.restrictScalars_iteratedFDeriv (𝕜 := ℝ))
  simp only [Function.comp_apply, ContinuousMultilinearMap.coe_restrictScalars,
    iteratedFDeriv_two_apply] at hH
  change (fderiv ℂ (fderiv ℂ f) x v) w = (fderiv ℝ (fderiv ℝ f) x v) w at hH
  rw [← hH, hD]
  rfl

/-- The three slots project to `0, 1, i` in the imaginary complex coordinates. -/
def imaginarySlot : Fin 3 → ℂ := ![0, 1, Complex.I]

def imaginaryDirection {ι : Type*} [DecidableEq ι] (a : ι) (α : Fin 3) : ι → ℂ :=
  imaginarySlot α • Pi.single a 1

/-- The actual three-slot Hessian of a function independent of real coordinates.
The zero projected direction records that its real-coordinate derivatives vanish. -/
def imaginaryHessian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : (ι → ℂ) → ℝ) (z : ι → ℂ) : Matrix ι ι Q :=
  hessianMap threeSlots (fun p q =>
    (fderiv ℝ (fderiv ℝ u) z (imaginaryDirection p.1 p.2)) (imaginaryDirection q.1 q.2))

def imaginaryGradient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : (ι → ℂ) → ℝ) (z : ι → ℂ) : ι → Q :=
  fun a => ∑ α : Fin 3, (fderiv ℝ u z (imaginaryDirection a α)) • threeSlots α

theorem imaginaryGradient_norm_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℂ) → ℂ} {z : ι → ℂ} (hf : DifferentiableAt ℂ f z) (a : ι) :
    imaginaryGradient (fun y => ‖f y‖ ^ 2) z a =
      (2 : ℝ) • (OAI.Analysis.Calculus.Current.complexK
        (star (fderiv ℂ f z (Pi.single a 1)) * f z) * OAI.Analysis.Calculus.Current.qi) := by
  have hd := (hf.hasFDerivAt.restrictScalars ℝ).norm_sq.fderiv
  simp only [imaginaryGradient, hd]
  simp only [two_smul,
    imaginaryDirection]
  ext <;> simp [imaginarySlot, threeSlots, OAI.Analysis.Calculus.Current.complexK, OAI.Analysis.Calculus.Current.qi,
    Fin.sum_univ_succ] ; ring

private theorem holomorphic_hessian_algebra (u ja jb h : ℂ) :
    (∑ α : Fin 3, ∑ β : Fin 3,
      (2 * (inner ℝ u (imaginarySlot α * imaginarySlot β * h) +
        inner ℝ (imaginarySlot α * ja) (imaginarySlot β * jb))) •
          (threeSlots α * star (threeSlots β))) =
      (4 : ℝ) • OAI.Analysis.Calculus.Current.complexK (star ja * jb) := by
  ext <;> simp [imaginarySlot, threeSlots, OAI.Analysis.Calculus.Current.complexK, Fin.sum_univ_succ] <;> ring

/-- The holomorphic-square Hessian identity from the manuscript, with actual
Fréchet derivatives rather than a prescribed Hessian array. -/
theorem imaginaryHessian_norm_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℂ) → ℂ} {z : ι → ℂ} (hf : ContDiffAt ℂ 2 f z) (a b : ι) :
    imaginaryHessian (fun y => ‖f y‖ ^ 2) z a b =
      (4 : ℝ) • OAI.Analysis.Calculus.Current.complexK
        (star (fderiv ℂ f z (Pi.single a 1)) * fderiv ℂ f z (Pi.single b 1)) := by
  have hD (c : ι) (α : Fin 3) :
      fderiv ℂ f z (imaginaryDirection c α) =
        imaginarySlot α * fderiv ℂ f z (Pi.single c 1) := by
    simp only [imaginaryDirection, map_smul, smul_eq_mul]
  have hH (α β : Fin 3) :
      (fderiv ℂ (fderiv ℂ f) z (imaginaryDirection a α)) (imaginaryDirection b β) =
        imaginarySlot α * imaginarySlot β *
          ((fderiv ℂ (fderiv ℂ f) z (Pi.single a 1)) (Pi.single b 1)) := by
    simp only [imaginaryDirection, map_smul, smul_apply, smul_eq_mul]
    ring
  simp only [imaginaryHessian, hessianMap, hessian_norm_sq_holomorphic hf, hD, hH]
  exact holomorphic_hessian_algebra _ _ _ _

theorem hessian_finset_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {κ : Type*} (s : Finset κ) (f : κ → E → ℝ) {x : E}
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x) (v w : E) :
    (fderiv ℝ (fderiv ℝ (fun y => ∑ i ∈ s, f i y)) x v) w =
      ∑ i ∈ s, (fderiv ℝ (fderiv ℝ (f i)) x v) w := by
  have heq : fderiv ℝ (fun y => ∑ i ∈ s, f i y) =ᶠ[𝓝 x]
      (fun y => ∑ i ∈ s, fderiv ℝ (f i) y) := by
    have he : ∀ᶠ y in 𝓝 x, ∀ i ∈ s, ContDiffAt ℝ 2 (f i) y := by
      apply (Filter.eventually_all_finset s).mpr
      intro i hi
      exact (hf i hi).eventually (by norm_num)
    filter_upwards [he] with y hy
    exact fderiv_fun_sum (fun i hi => (hy i hi).differentiableAt (by norm_num))
  rw [heq.fderiv_eq, fderiv_fun_sum (fun i hi =>
    ((hf i hi).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))]
  simp only [sum_apply]

theorem imaginaryHessian_sum {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (f : κ → (ι → ℂ) → ℝ) {z : ι → ℂ} (hf : ∀ i, ContDiffAt ℝ 2 (f i) z) :
    imaginaryHessian (fun y => ∑ i, f i y) z = ∑ i, imaginaryHessian (f i) z := by
  apply Matrix.ext
  intro a b
  simp only [imaginaryHessian, hessianMap, hessian_finset_sum _ _ (fun i _ => hf i),
    Finset.sum_smul, Matrix.sum_apply]
  conv_lhs =>
    arg 2
    ext α
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

theorem imaginaryHessian_sub_const {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℂ) → ℝ) (c : ℝ) (z : ι → ℂ) :
    imaginaryHessian (fun y => f y - c) z = imaginaryHessian f z := by
  have he : fderiv ℝ (fun y => f y - c) = fderiv ℝ f := by
    funext y
    exact fderiv_sub_const c
  simp only [imaginaryHessian, he]

theorem imaginaryGradient_sub_const {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℂ) → ℝ) (c : ℝ) (z : ι → ℂ) :
    imaginaryGradient (fun y => f y - c) z = imaginaryGradient f z := by
  funext a
  simp only [imaginaryGradient, fderiv_sub_const]

theorem imaginaryGradient_sum {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (f : κ → (ι → ℂ) → ℝ) {z : ι → ℂ} (hf : ∀ i, DifferentiableAt ℝ (f i) z) (a : ι) :
    imaginaryGradient (fun y => ∑ i, f i y) z a = ∑ i, imaginaryGradient (f i) z a := by
  simp only [imaginaryGradient, fderiv_fun_sum (fun i _ => hf i), sum_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

open scoped Matrix in
theorem imaginaryHessian_holomorphic_squares {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (f : κ → (ι → ℂ) → ℂ) {z : ι → ℂ} (hf : ∀ i, ContDiffAt ℂ 2 (f i) z) :
    imaginaryHessian (fun y => ∑ i, ‖f i y‖ ^ 2) z =
      (4 : ℝ) • ((Matrix.of (fun i a => OAI.Analysis.Calculus.Current.complexK
          (fderiv ℂ (f i) z (Pi.single a 1))))ᴴ *
        Matrix.of (fun i a => OAI.Analysis.Calculus.Current.complexK (fderiv ℂ (f i) z (Pi.single a 1)))) := by
  rw [imaginaryHessian_sum _ (fun i => (hf i).restrict_scalars ℝ |>.norm_sq ℂ)]
  apply Matrix.ext
  intro a b
  simp only [Matrix.sum_apply, imaginaryHessian_norm_sq (hf _), Matrix.smul_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, OAI.Analysis.Calculus.Current.complexK_star,
    ← map_mul, Finset.smul_sum]

end
end OAI.Analysis.Calculus.Quaternion
