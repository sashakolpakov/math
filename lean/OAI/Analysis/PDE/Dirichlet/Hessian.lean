import OAI.Analysis.Calculus.Quaternion.Algebra
import OAI.Analysis.PDE.Dirichlet.Maximum
import Mathlib.Analysis.InnerProductSpace.Laplacian

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion
open scoped Matrix

abbrev CoordinateSpace (m s : ℕ) := EuclideanSpace ℝ (Fin m × Fin s)

def coordinateVector {m s : ℕ} (i : Fin m × Fin s) : CoordinateSpace m s :=
  EuclideanSpace.single i 1

def realGradient {m s : ℕ} (f : CoordinateSpace m s → ℝ) (x : CoordinateSpace m s) :
    Fin m × Fin s → ℝ :=
  fun i ↦ fderiv ℝ f x (coordinateVector i)

/-- The ordinary real Hessian in the coordinate orthonormal basis. -/
def realHessian {m s : ℕ} (f : CoordinateSpace m s → ℝ) (x : CoordinateSpace m s) :
    Matrix (Fin m × Fin s) (Fin m × Fin s) ℝ :=
  fun i j ↦ (fderiv ℝ (fderiv ℝ f) x (coordinateVector i)) (coordinateVector j)

/-- The manuscript's quaternionic Hessian, applied to actual derivatives. -/
def quaternionHessian {m s : ℕ} (e : Fin s → Quaternion ℝ)
    (f : CoordinateSpace m s → ℝ) (x : CoordinateSpace m s) :
    Matrix (Fin m) (Fin m) (Quaternion ℝ) :=
  OAI.Analysis.Calculus.Quaternion.hessianMap e (realHessian f x)

def quaternionGradient {m s : ℕ} (e : Fin s → Quaternion ℝ)
    (f : CoordinateSpace m s → ℝ) (x : CoordinateSpace m s) : Fin m → Quaternion ℝ :=
  OAI.Analysis.Calculus.Quaternion.gradientMap e (realGradient f x)

theorem realHessian_add_smul {m s : ℕ} {f g : CoordinateSpace m s → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (c : ℝ) (x : CoordinateSpace m s) :
    realHessian (fun y ↦ f y + c • g y) x = realHessian f x + c • realHessian g x := by
  have hf₁ := hf.differentiable (by norm_num)
  have hg₁ := hg.differentiable (by norm_num)
  have hf₂ := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hg₂ := (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hD : fderiv ℝ (fun y ↦ f y + c • g y) =
      fun y ↦ fderiv ℝ f y + c • fderiv ℝ g y := by
    funext y
    exact ((hf₁ y).hasFDerivAt.add ((hg₁ y).hasFDerivAt.const_smul c)).fderiv
  have hD₂ : fderiv ℝ (fun y ↦ fderiv ℝ f y + c • fderiv ℝ g y) x =
      fderiv ℝ (fderiv ℝ f) x + c • fderiv ℝ (fderiv ℝ g) x :=
    ((hf₂ x).hasFDerivAt.add ((hg₂ x).hasFDerivAt.const_smul c)).fderiv
  apply Matrix.ext
  intro i j
  simp only [realHessian]
  rw [hD, hD₂]
  simp only [realHessian, add_apply, smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.smul_apply]

theorem quaternionHessian_add_smul {m s : ℕ} (e : Fin s → Quaternion ℝ)
    {f g : CoordinateSpace m s → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (c : ℝ) (x : CoordinateSpace m s) :
    quaternionHessian e (fun y ↦ f y + c • g y) x =
      quaternionHessian e f x + c • quaternionHessian e g x := by
  simp only [quaternionHessian, realHessian_add_smul hf hg, OAI.Analysis.Calculus.Quaternion.hessianMap_add, OAI.Analysis.Calculus.Quaternion.hessianMap_smul]

theorem realHessian_isSymm {m s : ℕ} {f : CoordinateSpace m s → ℝ}
    {x : CoordinateSpace m s} (hf : ContDiffAt ℝ 2 f x) :
    (realHessian f x).IsSymm := by
  apply Matrix.ext
  intro i j
  exact (hf.isSymmSndFDerivAt (by norm_num)).eq (coordinateVector j) (coordinateVector i)

theorem quaternionHessian_isHermitian {m s : ℕ} (e : Fin s → Quaternion ℝ)
    {f : CoordinateSpace m s → ℝ} {x : CoordinateSpace m s}
    (hf : ContDiffAt ℝ 2 f x) :
    (quaternionHessian e f x).IsHermitian :=
  OAI.Analysis.Calculus.Quaternion.hessianMap_isHermitian e _ (realHessian_isSymm hf)

/-- The coordinate trace agrees with mathlib's basis-independent Laplacian. -/
theorem realHessian_trace {m s : ℕ} (f : CoordinateSpace m s → ℝ)
    (x : CoordinateSpace m s) :
    Matrix.trace (realHessian f x) = Laplacian.laplacian f x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin m × Fin s) ℝ)]
  simp [Matrix.trace, Matrix.diag, realHessian, coordinateVector, iteratedFDeriv_two_apply]

theorem quaternionHessian_trace {m s : ℕ} (e : Fin s → Quaternion ℝ)
    (he : ∀ α β, (e α * star (e β)).re = if α = β then 1 else 0)
    {f : CoordinateSpace m s → ℝ} {x : CoordinateSpace m s}
    (hf : ContDiffAt ℝ 2 f x) :
    Matrix.trace (quaternionHessian e f x) =
      ((Laplacian.laplacian f x : ℝ) : Quaternion ℝ) := by
  rw [quaternionHessian, OAI.Analysis.Calculus.Quaternion.hessianMap_trace e he _ (realHessian_isSymm hf), realHessian_trace]

theorem hessian_norm_sq_bilinear {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x v w : E) : (fderiv ℝ (fderiv ℝ (fun y : E ↦ ‖y‖ ^ 2)) x v) w =
      2 * inner ℝ v w := by
  rw [fderiv_norm_sq, fderiv_const_smul (innerSL ℝ).differentiableAt]
  simp only [ContinuousLinearMap.fderiv, smul_apply]
  change (2 : ℕ) • (inner ℝ v w) = 2 * inner ℝ v w
  simp [two_smul, two_mul]

theorem realHessian_norm_sq {m s : ℕ} (x : CoordinateSpace m s) :
    realHessian (fun y : CoordinateSpace m s ↦ ‖y‖ ^ 2) x =
      (2 : ℝ) • (1 : Matrix (Fin m × Fin s) (Fin m × Fin s) ℝ) := by
  ext i j
  simp [realHessian, hessian_norm_sq_bilinear, coordinateVector,
    EuclideanSpace.inner_single_left, PiLp.single_apply, Matrix.one_apply]

/-- The genuine second-derivative product rule, evaluated on two real directions. -/
theorem hessian_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x v w : E) :
    (fderiv ℝ (fderiv ℝ (fun y ↦ f y * g y)) x v) w =
      f x * (fderiv ℝ (fderiv ℝ g) x v) w +
      g x * (fderiv ℝ (fderiv ℝ f) x v) w +
      fderiv ℝ f x v * fderiv ℝ g x w + fderiv ℝ g x v * fderiv ℝ f x w := by
  have hf₁ := hf.differentiable (by norm_num)
  have hg₁ := hg.differentiable (by norm_num)
  have hf₂ := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hg₂ := (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hD : fderiv ℝ (fun y ↦ f y * g y) =
      fun y ↦ f y • fderiv ℝ g y + g y • fderiv ℝ f y := by
    funext y
    exact fderiv_fun_mul (hf₁ y) (hg₁ y)
  have hD₂ := ((hf₁ x).hasFDerivAt.smul (hg₂ x).hasFDerivAt).add
    ((hg₁ x).hasFDerivAt.smul (hf₂ x).hasFDerivAt)
  have hD₂' := hD₂.fderiv
  simp only [Pi.add_def, Pi.smul_apply'] at hD₂'
  rw [hD, hD₂']
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

theorem realHessian_mul {m s : ℕ} {f g : CoordinateSpace m s → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : CoordinateSpace m s) :
    realHessian (fun y ↦ f y * g y) x =
      f x • realHessian g x + g x • realHessian f x +
      Matrix.of (fun i j ↦ realGradient f x i * realGradient g x j) +
      Matrix.of (fun i j ↦ realGradient g x i * realGradient f x j) := by
  ext i j
  exact hessian_mul hf hg x (coordinateVector i) (coordinateVector j)

theorem quaternionHessian_mul {m s : ℕ} (e : Fin s → Quaternion ℝ)
    {f g : CoordinateSpace m s → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x : CoordinateSpace m s) :
    quaternionHessian e (fun y ↦ f y * g y) x =
      f x • quaternionHessian e g x + g x • quaternionHessian e f x +
      Matrix.of (fun i j ↦ quaternionGradient e f x i * star (quaternionGradient e g x j)) +
      Matrix.of (fun i j ↦ quaternionGradient e g x i * star (quaternionGradient e f x j)) := by
  unfold quaternionHessian quaternionGradient
  rw [realHessian_mul hf hg]
  exact OAI.Analysis.Calculus.Quaternion.hessian_product_algebra e _ _ _ _ _ _

theorem realHessian_bilinear {m s : ℕ} (f : CoordinateSpace m s → ℝ)
    (x v w : CoordinateSpace m s) :
    (∑ i, ∑ j, v i * realHessian f x i j * w j) =
      (fderiv ℝ (fderiv ℝ f) x v) w := by
  have hv : (∑ i, v i • coordinateVector i) = v := by
    simpa [coordinateVector] using (EuclideanSpace.basisFun (Fin m × Fin s) ℝ).sum_repr v
  have hw : (∑ i, w i • coordinateVector i) = w := by
    simpa [coordinateVector] using (EuclideanSpace.basisFun (Fin m × Fin s) ℝ).sum_repr w
  symm
  calc
    (fderiv ℝ (fderiv ℝ f) x v) w =
        (fderiv ℝ (fderiv ℝ f) x (∑ i, v i • coordinateVector i))
          (∑ j, w j • coordinateVector j) := by rw [hv, hw]
    _ = _ := by
      simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      unfold realHessian
      ring

theorem realHessian_neg_posSemidef_of_localMax {m s : ℕ}
    {f : CoordinateSpace m s → ℝ} {x : CoordinateSpace m s}
    (hf : ContDiff ℝ 2 f) (hmax : IsLocalMax f x) :
    (-realHessian f x).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, ?_⟩
  · exact (Matrix.isHermitian_iff_isSymm.mpr (realHessian_isSymm hf.contDiffAt)).neg
  · intro z
    let v : CoordinateSpace m s := WithLp.toLp 2 z
    have h := hessian_nonpos_of_localMax hf hmax v
    rw [← realHessian_bilinear f x v v] at h
    have heq : star z ⬝ᵥ (-realHessian f x *ᵥ z) =
        -(∑ i, ∑ j, v i * realHessian f x i j * v j) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.neg_apply, Pi.star_apply, star_trivial,
        Finset.mul_sum, neg_mul, mul_neg, Finset.sum_neg_distrib]
      simp only [v, mul_assoc]
    rw [heq]
    exact neg_nonneg.mpr h

end OAI.Analysis.PDE.Dirichlet
