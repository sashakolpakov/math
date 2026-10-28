import OAI.NumberTheory.ArithmeticGroups.Lattices.BasisSpectralOperator
import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousOperatorExponentialDeterminant
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-! # Spectral Operator Exponential -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.SpectralOperatorExponential.Construction

noncomputable section

section

/-! Exponentiation acts on an eigenbasis by exponentiating each
eigenvalue. This identifies the positive spectral logarithm. -/

open scoped Classical _root_.Matrix.Norms.Operator
open NormedSpace

theorem basisSpectralEnd_toMatrix
    {L ι : Type*} [AddCommGroup L] [Module ℝ L] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ L) (w : ι → ℝ) :
    LinearMap.toMatrix b b (BasisSpectralOperator.Construction.basisSpectralEnd b w) = Matrix.diagonal w := by
  ext i j
  rw [LinearMap.toMatrix_apply, BasisSpectralOperator.Construction.basisSpectralEnd_apply_basis]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, b.repr_self_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, Ne.symm hij]

theorem basisSpectralEnd_exp
    {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : Module.Basis (Fin m) ℝ L) (w : Fin m → ℝ) :
    exp (BasisSpectralOperator.Construction.basisSpectralEnd b w).toContinuousLinearMap =
      (BasisSpectralOperator.Construction.basisSpectralEnd b (fun i => exp (w i))).toContinuousLinearMap := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  let : NormedAlgebra ℚ (L →L[ℝ] L) := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  have he := NormedSpace.map_exp (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b) (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix_continuous b)
    (BasisSpectralOperator.Construction.basisSpectralEnd b w).toContinuousLinearMap
  have hm : LinearMap.toMatrix b b (exp (BasisSpectralOperator.Construction.basisSpectralEnd b w).toContinuousLinearMap).toLinearMap =
      LinearMap.toMatrix b b (BasisSpectralOperator.Construction.basisSpectralEnd b (fun i => exp (w i))) := by
    change ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b (exp (BasisSpectralOperator.Construction.basisSpectralEnd b w).toContinuousLinearMap) = _
    rw [he]
    change exp (LinearMap.toMatrix b b (BasisSpectralOperator.Construction.basisSpectralEnd b w)) = _
    rw [basisSpectralEnd_toMatrix, Matrix.exp_diagonal, basisSpectralEnd_toMatrix]
    rw [Pi.exp_def]
  have hl := (LinearMap.toMatrix b b).injective hm
  apply ContinuousLinearMap.ext
  intro x
  exact DFunLike.congr_fun hl x

end

/-! A symmetric endomorphism is bounded by its exponential and inverse
exponential, with a constant depending only on dimension. -/

open scoped Classical
open _root_.ContinuousLinearMap NormedSpace

theorem exp_apply_eigenbasis
    {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : Module.Basis (Fin m) ℝ L) (w : Fin m → ℝ) (A : L →L[ℝ] L)
    (hA : ∀ i, A (b i) = w i • b i) (i : Fin m) :
    exp A (b i) = Real.exp (w i) • b i := by
  have hl := BasisSpectralOperator.Construction.basisSpectralEnd_eq_of_eigenbasis b w A.toLinearMap hA
  have he : (BasisSpectralOperator.Construction.basisSpectralEnd b w).toContinuousLinearMap = A := by
    ext x
    exact DFunLike.congr_fun hl x
  rw [← he, basisSpectralEnd_exp]
  change BasisSpectralOperator.Construction.basisSpectralEnd b (fun j => exp (w j)) (b i) = _
  rw [BasisSpectralOperator.Construction.basisSpectralEnd_apply_basis, ← Real.exp_eq_exp_ℝ]

theorem norm_le_card_mul_eigenvalue_bound
    {L ι : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [Fintype ι]
    (b : OrthonormalBasis ι ℝ L) (w : ι → ℝ) (A : L →L[ℝ] L)
    (hA : ∀ i, A (b i) = w i • b i) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ i, |w i| ≤ C) :
    ‖A‖ ≤ Fintype.card ι * C := by
  apply A.opNorm_le_bound (mul_nonneg (Nat.cast_nonneg _) hC)
  intro x
  have hc (i : ι) : |b.repr x i| ≤ ‖x‖ := by
    rw [b.repr_apply_apply, ← Real.norm_eq_abs]
    simpa only [b.norm_eq_one i, one_mul] using norm_inner_le_norm (b i) x
  have hn (i : ι) : ‖A (b i)‖ ≤ C := by
    rw [hA, norm_smul, b.norm_eq_one i, mul_one, Real.norm_eq_abs]
    exact hw i
  calc
    ‖A x‖ = ‖∑ i, b.repr x i • A (b i)‖ := by
      have he := congrArg A (b.sum_repr x)
      simp only [map_sum, map_smul] at he
      exact congrArg norm he.symm
    _ ≤ ∑ i, ‖b.repr x i • A (b i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ‖x‖ * C := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hc i) (hn i) (norm_nonneg _) (norm_nonneg _)
    _ = (Fintype.card ι * C) * ‖x‖ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem symmetric_norm_le_exponentials
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    (A : L →L[ℝ] L) (hA : A.toLinearMap.IsSymmetric) :
    ‖A‖ ≤ Module.finrank ℝ L * (‖exp A‖ + ‖exp (-A)‖) := by
  let b := hA.eigenvectorBasis rfl
  let w := hA.eigenvalues rfl
  have heig (i : Fin (Module.finrank ℝ L)) : A (b i) = w i • b i := hA.apply_eigenvectorBasis rfl i
  have hneg (i : Fin (Module.finrank ℝ L)) : (-A) (b i) = (-w i) • b i := by
    rw [neg_apply, heig, neg_smul]
  have hp (i : Fin (Module.finrank ℝ L)) : Real.exp (w i) ≤ ‖exp A‖ := by
    have h := (exp A).le_opNorm (b i)
    have he : exp A (b i) = Real.exp (w i) • b i := exp_apply_eigenbasis b.toBasis w A heig i
    rw [he, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), b.norm_eq_one i, mul_one, mul_one] at h
    exact h
  have hn (i : Fin (Module.finrank ℝ L)) : Real.exp (-w i) ≤ ‖exp (-A)‖ := by
    have h := (exp (-A)).le_opNorm (b i)
    have he : exp (-A) (b i) = Real.exp (-w i) • b i :=
      exp_apply_eigenbasis b.toBasis (fun i => -w i) (-A) hneg i
    rw [he, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), b.norm_eq_one i, mul_one, mul_one] at h
    exact h
  have hw (i : Fin (Module.finrank ℝ L)) : |w i| ≤ ‖exp A‖ + ‖exp (-A)‖ := by
    have h₁ := Real.add_one_le_exp (w i)
    have h₂ := Real.add_one_le_exp (-w i)
    apply abs_le.mpr
    constructor <;> nlinarith [hp i, hn i, norm_nonneg (exp A), norm_nonneg (exp (-A))]
  simpa only [Fintype.card_fin] using norm_le_card_mul_eigenvalue_bound b w A heig
    (‖exp A‖ + ‖exp (-A)‖) (add_nonneg (norm_nonneg _) (norm_nonneg _)) hw

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.SpectralOperatorExponential.Construction
