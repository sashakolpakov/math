import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.NormalizedCovariance
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SparseSpanning
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MovingTotalPeriod
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.OscillatorPhaseOrder

/-! # Reindex Theta -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ReindexTheta.CM

noncomputable section

section

/-! ThetaCycle: holomorphicity of the actual determinant multiplier along
holomorphic period families. A nonzero theta derivative determines the
multiplier locally as a quotient of actual holomorphic coefficients. -/

open scoped Classical _root_.Matrix.Norms.Elementwise _root_.Topology
open Filter

theorem finite_first_coefficient_span_eq_top {I : Type*} [Fintype I] (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) :
    Submodule.span ℂ (Set.range (fun φ : RepresentationTheory.Theta.DerivativeFactorizationDefinitions.Input I =>
      RepresentationTheory.Theta.DerivativeFactorizationDefinitions.firstCoefficient φ Z.matrix)) = ⊤ := by
  apply top_unique
  rw [← ComplexMultiplication.ThetaCoordinates.CM.span_coordinate_sparseThetaGradients_eq_top I Z.phase]
  apply Submodule.span_mono
  rintro l ⟨⟨a, n⟩, rfl⟩
  exact ⟨SparseSpanning.CM.sparseFiniteInput a n, SparseSpanning.CM.sparse_first_coefficient Z a n⟩

theorem exists_nonzero_first_coefficient (N : ℕ) (hN : 0 < N) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) :
    ∃ (φ : RepresentationTheory.Theta.DerivativeFactorizationDefinitions.Input (Fin N)) (u : Fin N → ℂ),
      RepresentationTheory.Theta.DerivativeFactorizationDefinitions.firstCoefficient φ Z.matrix u ≠ 0 := by
  by_contra h
  push Not at h
  have he : ∀ φ : RepresentationTheory.Theta.DerivativeFactorizationDefinitions.Input (Fin N), RepresentationTheory.Theta.DerivativeFactorizationDefinitions.firstCoefficient φ Z.matrix = 0 := by
    intro φ
    ext u
    exact h φ u
  have hle : Submodule.span ℂ (Set.range (fun φ : RepresentationTheory.Theta.DerivativeFactorizationDefinitions.Input (Fin N) =>
      RepresentationTheory.Theta.DerivativeFactorizationDefinitions.firstCoefficient φ Z.matrix)) ≤ ⊥ := by
    apply Submodule.span_le.mpr
    rintro l ⟨φ, rfl⟩
    simpa using he φ
  rw [finite_first_coefficient_span_eq_top Z] at hle
  have hp : (ContinuousLinearMap.proj (⟨0, hN⟩ : Fin N) : (Fin N → ℂ) →L[ℂ] ℂ) = 0 := by
    simpa using hle (show (ContinuousLinearMap.proj (⟨0, hN⟩ : Fin N) :
      (Fin N → ℂ) →L[ℂ] ℂ) ∈ (⊤ : Submodule ℂ _) from trivial)
  have hz := congrArg (fun f : (Fin N → ℂ) →L[ℂ] ℂ => f (fun _ => 1)) hp
  exact one_ne_zero hz

theorem normalized_first_coefficient_covariance (N : ℕ) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℚ)
    (φ : RepresentationTheory.Theta.DerivativeFactorizationDefinitions.Input (Fin N)) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) :
    (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.firstCoefficient (NormalizedCovariance.CM.normalizedFiniteOscillatorInput N γ φ)
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z).matrix).comp ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z) =
      NormalizedCovariance.CM.rationalThetaMultiplier N γ Z • RepresentationTheory.Theta.DerivativeFactorizationDefinitions.firstCoefficient φ Z.matrix := by
  apply ComplexMultiplication.ThetaCovariance.CM.theta_first_derivative_covariance ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z)
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).thetaCorrectionForm Z) (NormalizedCovariance.CM.rationalThetaMultiplier N γ Z)
    (RepresentationTheory.Theta.DerivativeFactorizationAdelicLattice.theta_hasFDerivAt_zero φ Z)
    (RepresentationTheory.Theta.DerivativeFactorizationAdelicLattice.theta_hasFDerivAt_zero (NormalizedCovariance.CM.normalizedFiniteOscillatorInput N γ φ)
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z))
  intro z
  simpa only [mul_assoc] using! NormalizedCovariance.CM.normalized_classical_theta_covariance N γ φ Z z

theorem jacobi_vector_holomorphic {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [Fintype I] [DecidableEq I] {s : Set V} (g : ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks I ℝ)
    (Z : V → ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (hZ : DifferentiableOn ℂ (fun x => (Z x).matrix) s) (u : I → ℂ) :
    DifferentiableOn ℂ (fun x => g.jacobiChange (Z x) u) s := by
  have hM : DifferentiableOn ℂ (fun x => g.complexify.denominator (Z x).matrix) s :=
    (MatrixCalculus.CM.matrix_product_holomorphic (fun _ => g.complexify.C) (fun x => (Z x).matrix)
      (differentiableOn_const _) hZ).add (differentiableOn_const _)
  have hi := MatrixCalculus.CM.matrix_inverse_holomorphic _ hM (fun x _ => (g.denominator_det_isUnit (Z x)).ne_zero)
  apply differentiableOn_pi.mpr
  intro i
  simp only [ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.jacobiChange_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  fun_prop

theorem rational_theta_multiplier_holomorphic {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (N : ℕ) (hN : 0 < N) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℚ) {s : Set V}
    (Z : V → ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (hZ : DifferentiableOn ℂ (fun x => (Z x).matrix) s) :
    DifferentiableOn ℂ (fun x => NormalizedCovariance.CM.rationalThetaMultiplier N γ (Z x)) s := by
  intro x hx
  obtain ⟨φ, u, hu⟩ := exists_nonzero_first_coefficient N hN (Z x)
  let Ψ := NormalizedCovariance.CM.normalizedFiniteOscillatorInput N γ φ
  let W := fun y => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel (Z y)
  let d := fun y => RepresentationTheory.Theta.DerivativeFactorizationDefinitions.firstCoefficient φ (Z y).matrix u
  let n := fun y => RepresentationTheory.Theta.DerivativeFactorizationDefinitions.firstCoefficient Ψ (W y).matrix ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange (Z y) u)
  have hd : DifferentiableOn ℂ d s := by
    have hc : DifferentiableOn ℂ (fun y => RepresentationTheory.Theta.DerivativeFactorizationDefinitions.firstCoefficient φ (Z y).matrix) s := by
      intro y hy
      simpa only [Function.comp_def] using!
        (RepresentationTheory.Theta.DerivativeFactorizationAdelicLattice.firstCoefficient_differentiableAt φ (Z y)).comp_differentiableWithinAt
          y (hZ y hy)
    exact hc.clm_apply (differentiableOn_const u)
  have hn : DifferentiableOn ℂ n s := by
    have hW := MovingTotalPeriod.CM.symplectic_period_holomorphic (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z hZ
    have hc : DifferentiableOn ℂ (fun y => RepresentationTheory.Theta.DerivativeFactorizationDefinitions.firstCoefficient Ψ (W y).matrix) s := by
      intro y hy
      simpa only [Function.comp_def] using!
        (RepresentationTheory.Theta.DerivativeFactorizationAdelicLattice.firstCoefficient_differentiableAt Ψ (W y)).comp_differentiableWithinAt
          y (hW y hy)
    exact hc.clm_apply (jacobi_vector_holomorphic (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z hZ u)
  have hp (y : V) : n y = NormalizedCovariance.CM.rationalThetaMultiplier N γ (Z y) * d y :=
    congrArg (fun f : (Fin N → ℂ) →L[ℂ] ℂ => f u) (normalized_first_coefficient_covariance N γ φ (Z y))
  have he : (fun y => NormalizedCovariance.CM.rationalThetaMultiplier N γ (Z y)) =ᶠ[𝓝[s] x] (fun y => n y / d y) := by
    have hne : ∀ᶠ y in 𝓝[s] x, d y ≠ 0 := (hd x hx).continuousWithinAt.eventually (eventually_ne_nhds hu)
    filter_upwards [hne] with y hy
    exact (eq_div_iff hy).mpr (hp y).symm
  have hr : DifferentiableWithinAt ℂ (fun y => n y / d y) s x := by
    simpa only [div_eq_mul_inv] using! (hn x hx).mul ((hd x hx).inv hu)
  exact hr.congr_of_eventuallyEq_of_mem he hx

end

section

/-! ThetaCycle: compare the constructed oscillator multiplier with an actual
continuous square-root frame. The single resulting sign is absorbed into
one finite Schwartz input, uniformly throughout a connected period family. -/

open scoped Classical
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

theorem rational_theta_multiplier_ne_zero (N : ℕ) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℚ)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) : NormalizedCovariance.CM.rationalThetaMultiplier N γ Z ≠ 0 :=
  div_ne_zero (NormalizedCovariance.CM.rational_oscillator_unit_scalar_ne_zero N γ)
    (RationalGaussianCovariance.CM.rational_gaussian_coefficient_ne_zero N γ Z)

theorem rational_theta_multiplier_frame_sign {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    (N : ℕ) (hN : 0 < N) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℚ) {s : Set V}
    (hs : IsPreconnected s) (Z : V → ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N))
    (hZ : DifferentiableOn ℂ (fun x => (Z x).matrix) s)
    (d : V → ℂ) (hd : ContinuousOn d s)
    (hsq : ∀ x ∈ s, d x ^ 2 = ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.denominator (Z x).matrix).det) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
      ∀ x ∈ s, d x = σ * NormalizedCovariance.CM.rationalThetaMultiplier N γ (Z x) := by
  have hm := (rational_theta_multiplier_holomorphic N hN γ Z hZ).continuousOn
  have he : Set.EqOn (d ^ 2) ((fun x => NormalizedCovariance.CM.rationalThetaMultiplier N γ (Z x)) ^ 2) s := by
    intro x hx
    exact (hsq x hx).trans (NormalizedCovariance.CM.rational_theta_multiplier_square N γ (Z x)).symm
  rcases hs.eq_or_eq_neg_of_sq_eq hd hm he
    (fun {x} _ => rational_theta_multiplier_ne_zero N γ (Z x)) with h | h
  · exact ⟨1, Or.inl rfl, fun x hx => (h hx).trans (one_mul _).symm⟩
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro x hx
    simpa only [Pi.neg_apply, neg_one_mul] using h hx

theorem exists_frame_normalized_finite_input {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    (N : ℕ) (hN : 0 < N) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℚ) {s : Set V}
    (hs : IsPreconnected s) (Z : V → ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N))
    (hZ : DifferentiableOn ℂ (fun x => (Z x).matrix) s)
    (d : V → ℂ) (hd : ContinuousOn d s)
    (hsq : ∀ x ∈ s, d x ^ 2 = ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.denominator (Z x).matrix).det)
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (Fin N)) :
    ∃ Ψ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (Fin N), ∀ x ∈ s, ∀ z : Fin N → ℂ,
      RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed Ψ ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel (Z x)) ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange (Z x) z) =
        d x * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ (Z x) z := by
  obtain ⟨σ, _, hσ⟩ := rational_theta_multiplier_frame_sign N hN γ hs Z hZ d hd hsq
  refine ⟨RepresentationTheory.Theta.Kernel.Factorization.scaleInput σ (NormalizedCovariance.CM.normalizedFiniteOscillatorInput N γ φ), ?_⟩
  intro x hx z
  rw [NormalizedCovariance.CM.completed_scale_finite_input, NormalizedCovariance.CM.normalized_completed_theta_covariance, hσ x hx, mul_assoc]

end

section

/-! ThetaCycle: transport the literal finite input, positive Siegel matrix, and
completed theta series through a finite coordinate equivalence. -/

open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

variable {I J : Type*} [Fintype I] [Fintype J]

def positionReindex {A : Type*} [TopologicalSpace A] (e : I ≃ J) : (I → A) ≃ₜ (J → A) where
  toFun x j := x (e.symm j)
  invFun x i := x (e i)
  left_inv x := by funext i; simp only [Equiv.symm_apply_apply]
  right_inv x := by funext j; simp only [Equiv.apply_symm_apply]
  continuous_toFun := continuous_pi (fun j => continuous_apply (e.symm j))
  continuous_invFun := continuous_pi (fun i => continuous_apply (e i))

def finiteInputReindex (e : I ≃ J) : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input I ≃ RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input J :=
  RationalSchwartzCoordinates.CM.finiteSchwartzHomeomorphEquiv (positionReindex (A := RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.AQf) e).symm

omit [Fintype I] [Fintype J] in
theorem finite_input_reindex_apply (e : I ≃ J) (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input I) (x : J → RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.AQf) :
    (finiteInputReindex e φ).val x = φ.val (fun i => x (e i)) := rfl

def siegelReindex (e : I ≃ J) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix J where
  matrix := Matrix.reindex e e Z.matrix
  symmetric := Z.symmetric.submatrix e.symm
  imaginary_posDef := Z.imaginary_posDef.submatrix e.symm.injective

theorem reindex_double_sum {R : Type*} [AddCommMonoid R] (e : I ≃ J) (f : I → I → R) :
    (∑ i : J, ∑ j : J, f (e.symm i) (e.symm j)) = ∑ i : I, ∑ j : I, f i j := by
  calc
    _ = ∑ i : J, ∑ j : I, f (e.symm i) j := by
      apply Finset.sum_congr rfl
      intro i _
      exact e.symm.sum_comp (f (e.symm i))
    _ = _ := e.symm.sum_comp (fun i => ∑ j : I, f i j)

theorem kernel_reindex (e : I ≃ J) (B : Matrix I I ℂ) (x : I → ℚ) (z : I → ℂ) :
    RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.kernel (Matrix.reindex e e B) (fun j => x (e.symm j)) (fun j => z (e.symm j)) = RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.kernel B x z := by
  unfold RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.kernel
  congr 1
  simp only [ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm_apply, ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing_apply, RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.realPosition,
    Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [reindex_double_sum e (fun i j => ((x i : ℝ) : ℂ) * (((x j : ℝ) : ℂ) * B i j)),
    e.symm.sum_comp (fun i => ((x i : ℝ) : ℂ) * z i)]

theorem theta_reindex (e : I ≃ J) (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input I) (B : Matrix I I ℂ) (z : I → ℂ) :
    RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.theta (finiteInputReindex e φ) (Matrix.reindex e e B) (fun j => z (e.symm j)) = RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.theta φ B z := by
  unfold RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.theta
  rw [← (Equiv.piCongrLeft' (fun _ : I => ℚ) e).tsum_eq]
  apply tsum_congr
  intro x
  change (finiteInputReindex e φ).val (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.diagonal (fun j => x (e.symm j))) *
    RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.kernel (Matrix.reindex e e B) (fun j => x (e.symm j)) (fun j => z (e.symm j)) = _
  rw [kernel_reindex, finite_input_reindex_apply]
  simp only [RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.diagonal, Equiv.symm_apply_apply]
  rfl

theorem completion_form_reindex (e : I ≃ J) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (z w : I → ℂ) :
    (siegelReindex e Z).completionForm (fun j => z (e.symm j)) (fun j => w (e.symm j)) =
      Z.completionForm z w := by
  rw [ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.completionForm_apply, ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.completionForm_apply]
  have hi : (fun i j => ((siegelReindex e Z).matrix i j).im) =
      Matrix.reindex e e (fun i j => (Z.matrix i j).im) := rfl
  rw [hi]
  have hinv := Matrix.inv_reindex e e (fun i j => (Z.matrix i j).im)
  rw [hinv]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [reindex_double_sum e (fun i j => z i *
    ((@Inv.inv (Matrix I I ℝ) Matrix.inv (fun k l => (Z.matrix k l).im) i j) : ℂ) * w j)]

theorem completed_reindex (e : I ≃ J) (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input I) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (z : I → ℂ) :
    RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (finiteInputReindex e φ) (siegelReindex e Z) (fun j => z (e.symm j)) =
      RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z z := by
  unfold RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor
  rw [completion_form_reindex]
  change _ * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.theta (finiteInputReindex e φ) (Matrix.reindex e e Z.matrix) _ = _
  rw [theta_reindex]

end

/-! ThetaCycle: coordinate equivariance of the actual fractional Siegel action,
its determinant denominator, and its Jacobi change of variables. -/

open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem reindex_rational_denominator (e : I ≃ J) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) :
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (OscillatorPhaseOrder.CM.reindexSymplectic e γ)).complexify.denominator (siegelReindex e Z).matrix =
      Matrix.reindex e e ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.denominator Z.matrix) := by
  change Matrix.reindex e e (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.C * Matrix.reindex e e Z.matrix +
    Matrix.reindex e e (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.D = _
  exact ((Matrix.reindexRingEquiv ℂ e).map_add
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.C * Z.matrix) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.D).trans
      (congrArg (fun M => M + Matrix.reindex e e (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.D)
        ((Matrix.reindexRingEquiv ℂ e).map_mul (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.C Z.matrix)) |>.symm

theorem reindex_rational_numerator (e : I ≃ J) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) :
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (OscillatorPhaseOrder.CM.reindexSymplectic e γ)).complexify.numerator (siegelReindex e Z).matrix =
      Matrix.reindex e e ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.numerator Z.matrix) := by
  change Matrix.reindex e e (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.A * Matrix.reindex e e Z.matrix +
    Matrix.reindex e e (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.B = _
  exact ((Matrix.reindexRingEquiv ℂ e).map_add
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.A * Z.matrix) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.B).trans
      (congrArg (fun M => M + Matrix.reindex e e (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.B)
        ((Matrix.reindexRingEquiv ℂ e).map_mul (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.A Z.matrix)) |>.symm

omit [DecidableEq I] in
theorem siegel_matrix_ext {A B : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I} (h : A.matrix = B.matrix) : A = B := by
  cases A
  cases B
  cases h
  rfl

theorem reindex_rational_siegel_action (e : I ≃ J) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) :
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (OscillatorPhaseOrder.CM.reindexSymplectic e γ)).transformSiegel (siegelReindex e Z) =
      siegelReindex e ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z) := by
  apply siegel_matrix_ext
  change (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (OscillatorPhaseOrder.CM.reindexSymplectic e γ)).complexify.numerator (siegelReindex e Z).matrix *
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (OscillatorPhaseOrder.CM.reindexSymplectic e γ)).complexify.denominator (siegelReindex e Z).matrix)⁻¹ = _
  rw [reindex_rational_numerator, reindex_rational_denominator, Matrix.inv_reindex]
  exact ((Matrix.reindexRingEquiv ℂ e).map_mul _ _).symm

omit [DecidableEq I] [DecidableEq J] in
theorem reindex_matrix_mul_vec (e : I ≃ J) (M : Matrix I I ℂ) (z : I → ℂ) :
    Matrix.reindex e e M *ᵥ (fun j => z (e.symm j)) = fun j => (M *ᵥ z) (e.symm j) := by
  funext j
  exact e.symm.sum_comp (fun i => M (e.symm j) i * z i)

theorem reindex_rational_jacobi_action (e : I ≃ J) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (z : I → ℂ) :
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (OscillatorPhaseOrder.CM.reindexSymplectic e γ)).jacobiChange (siegelReindex e Z) (fun j => z (e.symm j)) =
      fun j => ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z z) (e.symm j) := by
  rw [ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.jacobiChange_apply, reindex_rational_denominator, Matrix.inv_reindex]
  change Matrix.reindex e e (((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.denominator Z.matrix)⁻¹).transpose *ᵥ
    (fun j => z (e.symm j)) = _
  exact reindex_matrix_mul_vec e _ z

theorem reindex_rational_denominator_det (e : I ≃ J) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) :
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (OscillatorPhaseOrder.CM.reindexSymplectic e γ)).complexify.denominator (siegelReindex e Z).matrix).det =
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.denominator Z.matrix).det := by
  rw [reindex_rational_denominator]
  exact Matrix.det_reindex_self e _

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ReindexTheta.CM
