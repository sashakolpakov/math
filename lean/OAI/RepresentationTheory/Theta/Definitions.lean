import Mathlib
import OAI.AlgebraicGeometry.ComplexMultiplication.WeightedTheta
import OAI.AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion

/-! # Definitions -/

namespace OAI.RepresentationTheory.Theta.Definitions

noncomputable section

section

/-!
Definitions from the committed CompletedTheta specification, reproduced in a unique
namespace so the proof does not import the statement's sorry theorem.
-/

open scoped Classical _root_.Matrix BoundedContinuousFunction
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix-coordinate theta sum; a support lattice represents the
restriction of a finite Schwartz–Bruhat input to rational positions. -/
def theta
    (L : Submodule ℤ (ι → ℝ)) (φ : L →ᵇ ℂ)
    (Z : Matrix ι ι ℂ) (z : ι → ℂ) : ℂ :=
  ∑' x : L,
    φ x * Complex.exp
      ((Real.pi : ℂ) * Complex.I *
          AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z (x : ι → ℝ) (x : ι → ℝ) +
        (2 * (Real.pi : ℂ) * Complex.I) *
          (∑ i, (((x : ι → ℝ) i : ℝ) : ℂ) * z i))

/-- `exp ((π/2) zᵀ (Im Z)⁻¹ z) θφ(Z,z)`. -/
def completedTheta
    (L : Submodule ℤ (ι → ℝ)) (φ : L →ᵇ ℂ)
    (Z : Matrix ι ι ℂ) (z : ι → ℂ) : ℂ :=
  AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor
      (((Real.pi : ℂ) / 2) •
        AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear ((AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z)⁻¹)) z *
    theta L φ Z z

/-- Taylor coefficient, with the `1/a!` normalization. -/
def completedTensor
    (L : Submodule ℤ (ι → ℝ)) (φ : L →ᵇ ℂ)
    (a : ℕ) (Z : Matrix ι ι ℂ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin a => ι → ℂ) ℂ :=
  ((Nat.factorial a : ℂ)⁻¹) •
    iteratedFDeriv ℂ a (completedTheta L φ Z) 0

def siegelDomain : Set (Matrix ι ι ℂ) :=
  {Z | Z.IsSymm ∧ Matrix.PosDef (fun i j => (Z i j).im)}

end

/-! Parameter-dependent Taylor tensors and the inverse imaginary matrix. -/

open scoped Classical _root_.Matrix ContDiff _root_.Matrix.Norms.Elementwise

theorem partial_iteratedFDeriv_contDiffAt
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    {f : E → F → G} {x : E} {z : F}
    (h : ContDiffAt ℂ ω (Function.uncurry f) (x, z)) (a : ℕ) :
    ContDiffAt ℂ ω
      (fun w : E × F => iteratedFDeriv ℂ a (f w.1) w.2) (x, z) := by
  induction a with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def, Function.uncurry_def] using!
      h.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℂ F G).symm : G →L[ℂ] F [×0]→L[ℂ] G)
  | succ a ih =>
    have hc : ContDiffAt ℂ ω
        (fun w : (E × F) × F => iteratedFDeriv ℂ a (f w.1.1) w.2)
        ((x, z), z) :=
      ih.comp ((x, z), z) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hd : ContDiffAt ℂ ω
        (fun w : E × F => fderiv ℂ (iteratedFDeriv ℂ a (f w.1)) w.2) (x, z) :=
      hc.fderiv contDiffAt_snd (by simp)
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def, Function.uncurry_def] using!
      hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (a + 1) => F) G).symm :
          (F →L[ℂ] F [×a]→L[ℂ] G) →L[ℂ] F [×(a + 1)]→L[ℂ] G)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_det_contDiff : ContDiff ℝ ω (Matrix.det : Matrix ι ι ℂ → ℂ) := by
  change ContDiff ℝ ω (fun A : Matrix ι ι ℂ => A.det)
  simp only [Matrix.det_apply']
  fun_prop

theorem matrix_adjugate_contDiff :
    ContDiff ℝ ω (Matrix.adjugate : Matrix ι ι ℂ → Matrix ι ι ℂ) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [Matrix.adjugate_apply]
  apply matrix_det_contDiff.comp
  apply contDiff_pi.mpr
  intro k
  apply contDiff_pi.mpr
  intro l
  simp only [Matrix.updateRow_apply]
  split_ifs <;> fun_prop

theorem matrix_inverse_contDiffAt (M : Matrix ι ι ℂ) (hM : IsUnit M.det) :
    ContDiffAt ℝ ω (fun A : Matrix ι ι ℂ => A⁻¹) M := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact (matrix_det_contDiff.contDiffAt.inv hM.ne_zero).smul
    matrix_adjugate_contDiff.contDiffAt

theorem inverse_imaginary_contDiffAt (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    ContDiffAt ℝ ω (fun A : Matrix ι ι ℂ => (AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary A)⁻¹) Z.matrix := by
  apply (matrix_inverse_contDiffAt _ Z.matrixImaginary_det_isUnit).comp Z.matrix
  change ContDiffAt ℝ ω (fun A : Matrix ι ι ℂ => fun i j =>
    Complex.ofRealCLM (Complex.imCLM (A i j))) Z.matrix
  fun_prop

end

end OAI.RepresentationTheory.Theta.Definitions
