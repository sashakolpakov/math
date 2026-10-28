import OAI.RepresentationTheory.Theta.Analytic
import OAI.RepresentationTheory.Theta.Definitions

/-! # Completion Analysis -/

namespace OAI.RepresentationTheory.Theta.CompletionAnalysis

noncomputable section

section

/-! The independent quadratic parameter makes the completed jets smooth. -/

open scoped Classical _root_.Matrix ContDiff _root_.Matrix.Norms.Elementwise BoundedContinuousFunction
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def auxiliaryTheta (L : Submodule ℤ (ι → ℝ)) (φ : L →ᵇ ℂ)
    (p : Matrix ι ι ℂ × Matrix ι ι ℂ) (z : ι → ℂ) : ℂ :=
  AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor (((Real.pi : ℂ) / 2) • AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear p.2) z *
    Definitions.theta L φ p.1 z

omit [DecidableEq ι] in
theorem quadratic_factor_contDiff :
    ContDiff ℂ ω (fun w : (Matrix ι ι ℂ × Matrix ι ι ℂ) × (ι → ℂ) =>
      AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor (((Real.pi : ℂ) / 2) • AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear w.1.2) w.2) := by
  simp only [AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor, _root_.smul_apply, smul_eq_mul,
    AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear_apply, dotProduct, mulVec]
  fun_prop

omit [DecidableEq ι] in
theorem auxiliaryTheta_contDiffAt
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] (φ : L →ᵇ ℂ)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (W : Matrix ι ι ℂ) (z : ι → ℂ) :
    ContDiffAt ℂ ω (Function.uncurry (auxiliaryTheta L φ)) ((Z.matrix, W), z) := by
  have hθ : ContDiffAt ℂ ω
      (fun w : Matrix ι ι ℂ × (ι → ℂ) => Definitions.theta L φ w.1 w.2) (Z.matrix, z) :=
    (Analytic.theta_joint_analytic L φ Z z).contDiffAt
  have hc : ContDiffAt ℂ ω
      (fun w : (Matrix ι ι ℂ × Matrix ι ι ℂ) × (ι → ℂ) => (w.1.1, w.2))
      ((Z.matrix, W), z) := by fun_prop
  have hr : ContDiffAt ℂ ω
      (fun w : (Matrix ι ι ℂ × Matrix ι ι ℂ) × (ι → ℂ) => Definitions.theta L φ w.1.1 w.2)
      ((Z.matrix, W), z) := by
    simpa only [Function.comp_def] using! (hθ.comp ((Z.matrix, W), z) hc)
  exact quadratic_factor_contDiff.contDiffAt.mul hr

theorem completedTheta_contDiff
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] (φ : L →ᵇ ℂ)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) : ContDiff ℂ ω (Definitions.completedTheta L φ Z.matrix) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact (auxiliaryTheta_contDiffAt L φ Z ((AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z.matrix)⁻¹) z).comp z
    (contDiffAt_const.prodMk contDiffAt_id)

theorem completedTensor_contDiffAt
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] (φ : L →ᵇ ℂ)
    (a : ℕ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    ContDiffAt ℝ ω (Definitions.completedTensor L φ a) Z.matrix := by
  let W := (AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z.matrix)⁻¹
  have hj : ContDiffAt ℂ ω
      (fun p : Matrix ι ι ℂ × Matrix ι ι ℂ =>
        iteratedFDeriv ℂ a (auxiliaryTheta L φ p) 0) (Z.matrix, W) :=
    (Definitions.partial_iteratedFDeriv_contDiffAt
      (auxiliaryTheta_contDiffAt L φ Z W 0) a).comp (Z.matrix, W)
        (contDiffAt_id.prodMk contDiffAt_const)
  have hc : ContDiffAt ℝ ω
      (fun A : Matrix ι ι ℂ => (A, (AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary A)⁻¹)) Z.matrix :=
    contDiffAt_id.prodMk (Definitions.inverse_imaginary_contDiffAt Z)
  exact ((hj.restrict_scalars ℝ).comp Z.matrix hc).const_smul
    ((Nat.factorial a : ℂ)⁻¹)

theorem completedTensor_smooth
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] (φ : L →ᵇ ℂ) (a : ℕ) :
    ContDiffOn ℝ ⊤ (Definitions.completedTensor L φ a) Definitions.siegelDomain := by
  intro A hA
  exact ((completedTensor_contDiffAt L φ a ⟨A, hA.1, hA.2⟩).of_le le_top).contDiffWithinAt

theorem completedTensor_symmetric
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] (φ : L →ᵇ ℂ)
    (a : ℕ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (σ : Equiv.Perm (Fin a))
    (v : Fin a → (ι → ℂ)) :
    Definitions.completedTensor L φ a Z.matrix (fun i => v (σ i)) =
      Definitions.completedTensor L φ a Z.matrix v := by
  have h := ((completedTheta_contDiff L φ Z).contDiffAt (x := 0)).iteratedFDeriv_comp_perm v σ
  simpa only [Definitions.completedTensor, _root_.smul_apply, smul_eq_mul, Function.comp_def]
    using! congrArg (fun t : ℂ => (Nat.factorial a : ℂ)⁻¹ * t) h

end

/-!
# CompletedTheta: transformation of completed theta tensors

This proves the committed coordinate specification, using its uncompleted
functional equation as the explicit hypothesis `h_PoissonAutomorphy_Poisson` (called
`hPoisson` in Statements/CompletedTheta.lean). Its Gaussian cocycle agrees with the last
clause of corrected PoissonAutomorphy, but the two hypotheses are not literally identical:
PoissonAutomorphy sums finite Schwartz inputs over rational positions, whereas this target
sums bounded inputs over real discrete lattices. No statement stub is used.

PrescribedSigns supplies positive period data upstream, while LocalWeil supplies local Weil
formulas upstream of PoissonAutomorphy; neither is needed once the target's Siegel matrices
and uncompleted functional equation are given. Rationality and the specified
half-determinant square are retained, although cancellation and differentiation
work for any scalar multiplier satisfying the given functional equation.

As in the committed target, bounded restrictions to discrete lattices model
the finite inputs. The adelic-to-lattice interface is not asserted here: the
target already assumes its coordinate functional equation. No additional
substantive hypothesis is imposed. `Compatibility.lean` isolates the
transfer from corrected PoissonAutomorphy for arbitrary lattice presentations.
`Arithmetic.lean` constructs the source's arithmetic data and proves
both theta-sum identifications, using PoissonAutomorphy's normalized finite-action and
half-determinant pair. The elementwise matrix norm provides the standard
finite-dimensional coordinate calculus.
-/

open scoped Classical _root_.Matrix ContDiff _root_.Matrix.Norms.Elementwise BoundedContinuousFunction
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem completedTheta_eq_completionForm
    (L : Submodule ℤ (ι → ℝ)) (φ : L →ᵇ ℂ)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    Definitions.completedTheta L φ Z.matrix z =
      AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor Z.completionForm z * Definitions.theta L φ Z.matrix z := by
  simp only [Definitions.completedTheta, AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor, _root_.smul_apply,
    smul_eq_mul, AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear_apply, Z.completionForm_quadratic]

theorem completedTheta_covariance
    (L Lnew : Submodule ℤ (ι → ℝ)) (φ : L →ᵇ ℂ) (φnew : Lnew →ᵇ ℂ)
    (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (c : ℂ)
    (h_PoissonAutomorphy_Poisson : ∀ z : ι → ℂ,
      Definitions.theta Lnew φnew (g.transformSiegel Z).matrix (g.jacobiChange Z z) =
        c * (Complex.exp (g.thetaCorrectionForm Z z z) * Definitions.theta L φ Z.matrix z))
    (z : ι → ℂ) :
    Definitions.completedTheta Lnew φnew (g.transformSiegel Z).matrix (g.jacobiChange Z z) =
      c * Definitions.completedTheta L φ Z.matrix z := by
  rw [completedTheta_eq_completionForm, completedTheta_eq_completionForm]
  exact AlgebraicGeometry.ComplexMultiplication.ThetaCovariance.CM.theta_completion_covariance (g.jacobiChange Z) Z.completionForm
    (g.transformSiegel Z).completionForm (g.thetaCorrectionForm Z) c
    (Definitions.theta L φ Z.matrix) (Definitions.theta Lnew φnew (g.transformSiegel Z).matrix)
    h_PoissonAutomorphy_Poisson (g.completion_correction_identity Z) z

theorem completedTensor_covariance
    (L Lnew : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [DiscreteTopology Lnew]
    (φ : L →ᵇ ℂ) (φnew : Lnew →ᵇ ℂ)
    (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (c : ℂ)
    (h_PoissonAutomorphy_Poisson : ∀ z : ι → ℂ,
      Definitions.theta Lnew φnew (g.transformSiegel Z).matrix (g.jacobiChange Z z) =
        c * (Complex.exp (g.thetaCorrectionForm Z z z) * Definitions.theta L φ Z.matrix z))
    (a : ℕ) (v : Fin a → (ι → ℂ)) :
    Definitions.completedTensor Lnew φnew a (g.transformSiegel Z).matrix
        (fun i => g.jacobiChange Z (v i)) =
      c * Definitions.completedTensor L φ a Z.matrix v := by
  have heq : Definitions.completedTheta Lnew φnew (g.transformSiegel Z).matrix ∘
      g.jacobiChange Z = c • Definitions.completedTheta L φ Z.matrix :=
    funext (completedTheta_covariance L Lnew φ φnew g Z c h_PoissonAutomorphy_Poisson)
  have hd := congrArg (fun f : (ι → ℂ) → ℂ => iteratedFDeriv ℂ a f 0) heq
  rw [(g.jacobiChange Z).iteratedFDeriv_comp_right
      (completedTheta_contDiff Lnew φnew (g.transformSiegel Z)) 0 (by simp),
    iteratedFDeriv_const_smul_apply
      ((completedTheta_contDiff L φ Z).contDiffAt.of_le (by simp))] at hd
  have hv := congrArg (fun T => T v) hd
  simp only [map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    _root_.smul_apply, smul_eq_mul] at hv
  simp only [Definitions.completedTensor, _root_.smul_apply, smul_eq_mul, hv]
  ring

/-- The complete CompletedTheta conclusion, conditional on its stated Weil/Poisson input. -/
theorem completed_theta_tensor_transformation
    (L Lnew : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [DiscreteTopology Lnew]
    (φ : L →ᵇ ℂ) (φnew : Lnew →ᵇ ℂ)
    (gQ : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℚ)
    (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ)
    (_hA : g.A = gQ.A.map (algebraMap ℚ ℝ))
    (_hB : g.B = gQ.B.map (algebraMap ℚ ℝ))
    (_hC : g.C = gQ.C.map (algebraMap ℚ ℝ))
    (_hD : g.D = gQ.D.map (algebraMap ℚ ℝ))
    (halfDet : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι → ℂ)
    (_h_E24_halfDet : ∀ Z,
      halfDet Z ^ 2 = (g.complexify.denominator Z.matrix).det)
    (h_PoissonAutomorphy_Poisson : ∀ (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ),
      Definitions.theta Lnew φnew (g.transformSiegel Z).matrix (g.jacobiChange Z z) =
        halfDet Z * (Complex.exp (g.thetaCorrectionForm Z z z) * Definitions.theta L φ Z.matrix z)) :
    (∀ a : ℕ, ContDiffOn ℝ ⊤ (Definitions.completedTensor L φ a) Definitions.siegelDomain) ∧
    (∀ (a : ℕ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι)
        (σ : Equiv.Perm (Fin a)) (v : Fin a → (ι → ℂ)),
      Definitions.completedTensor L φ a Z.matrix (fun i => v (σ i)) =
        Definitions.completedTensor L φ a Z.matrix v) ∧
    (∀ (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ),
      Definitions.completedTheta Lnew φnew (g.transformSiegel Z).matrix (g.jacobiChange Z z) =
        halfDet Z * Definitions.completedTheta L φ Z.matrix z) ∧
    (∀ (a : ℕ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (v : Fin a → (ι → ℂ)),
      Definitions.completedTensor Lnew φnew a (g.transformSiegel Z).matrix
          (fun i => g.jacobiChange Z (v i)) =
        halfDet Z * Definitions.completedTensor L φ a Z.matrix v) := by
  refine ⟨completedTensor_smooth L φ, completedTensor_symmetric L φ, ?_, ?_⟩
  · intro Z z
    exact completedTheta_covariance L Lnew φ φnew g Z (halfDet Z) (h_PoissonAutomorphy_Poisson Z) z
  · intro a Z v
    exact completedTensor_covariance L Lnew φ φnew g Z (halfDet Z) (h_PoissonAutomorphy_Poisson Z) a v

end

end OAI.RepresentationTheory.Theta.CompletionAnalysis
