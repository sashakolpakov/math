import OAI.RepresentationTheory.Weil.Local.RealDiagonalNormalization
import OAI.RepresentationTheory.Weil.Local.SymmetricSquareLift

/-! # Reflection Algebra -/

namespace OAI.RepresentationTheory.Weil.Local.ReflectionAlgebra.Construction

noncomputable section

/-! Diagonal reflections and their quadratic identities. -/

open _root_.Matrix _root_.MeasureTheory

def diagonalReflection {k : Type} [Field k] {n : ℕ}
    (a : Fin n → k) (ha : ∀ i, a i ^ 2 = 1) : FunctionsMetaplectic.Construction.GeneralLinear k n where
  val := diagonal a
  inv := diagonal a
  val_inv := by
    have hh (i : Fin n) : a i * a i = 1 := (pow_two (a i)).symm.trans (ha i)
    simp [diagonal_mul_diagonal, hh]
  inv_val := by
    have hh (i : Fin n) : a i * a i = 1 := (pow_two (a i)).symm.trans (ha i)
    simp [diagonal_mul_diagonal, hh]

theorem diagonalReflection_inv {k : Type} [Field k] {n : ℕ}
    (a : Fin n → k) (ha : ∀ i, a i ^ 2 = 1) : (diagonalReflection a ha)⁻¹ = diagonalReflection a ha := rfl

theorem diagonalReflection_square {k : Type} [Field k] {n : ℕ}
    (a : Fin n → k) (ha : ∀ i, a i ^ 2 = 1) : diagonalReflection a ha * diagonalReflection a ha = 1 := by
  exact mul_inv_cancel (diagonalReflection a ha)

theorem diagonal_reflection_quadratic {k : Type} [Field k] {n : ℕ}
    (a : Fin n → k) (ha : ∀ i, a i ^ 2 = 1) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.quadratic (diagonal a) (fun i => a i * x i) = FunctionsMetaplectic.Construction.quadratic (diagonal a) x := by
  rw [RealDiagonalFresnel.Construction.quadratic_diagonal, RealDiagonalFresnel.Construction.quadratic_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow, ha i, one_mul]

theorem diagonal_reflection_complete_square
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (a : Fin n → k) (ha : ∀ i, a i ^ 2 = 1) (x y : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.quadratic (diagonal a) (y + fun i => a i * x i) - FunctionsMetaplectic.Construction.dot x (y + fun i => a i * x i) =
      FunctionsMetaplectic.Construction.quadratic (diagonal a) y - FunctionsMetaplectic.Construction.quadratic (diagonal a) x := by
  simp only [RealDiagonalFresnel.Construction.quadratic_diagonal, FunctionsMetaplectic.Construction.dot, Pi.add_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  linear_combination (x i * y i + a i * x i ^ 2 / 2) * (ha i)

theorem diagonalReflection_modulus
    {k : Type} [NormedField k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
    {n : ℕ} (a : Fin n → k) (ha : ∀ i, a i ^ 2 = 1) :
    FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k (diagonalReflection a ha)) = 1 := by
  let d := FunctionsMetaplectic.Construction.determinantUnit k (diagonalReflection a ha)
  have hd : d * d = 1 := by
    dsimp [d]
    rw [← LinearOscillatorHom.Construction.determinantUnit_mul, diagonalReflection_square]
    apply Units.ext
    simp [FunctionsMetaplectic.Construction.determinantUnit]
  have h := congrArg (FunctionsMetaplectic.Construction.localModulus k) hd
  rw [FunctionsMetaplectic.Construction.localModulus_mul, FunctionsMetaplectic.Construction.localModulus_one] at h
  have hpos := FunctionsMetaplectic.Construction.localModulus_pos k d
  change FunctionsMetaplectic.Construction.localModulus k d = 1
  nlinarith

theorem linearOscillator_diagonalReflection_apply
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    {n : ℕ} (ψ : AddChar k ℂ) (a : Fin n → k) (ha : ∀ i, a i ^ 2 = 1)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) :
    ((LinearIntertwiner.Construction.linearOscillator ψ (diagonalReflection a ha)).val.2 f).val x = f.val (fun i => a i * x i) := by
  rw [LinearIntertwiner.Construction.linearOscillator_apply, diagonalReflection_modulus, Real.sqrt_one,
    Complex.ofReal_one, inv_one, one_mul, diagonalReflection_inv]
  change f.val ((diagonal a).mulVec x) = _
  exact congrArg f.val (funext (fun i => Matrix.mulVec_diagonal a x i))

theorem reflection_weyl_factorization
    {k : Type} [Field k] {n : ℕ} (a : Fin n → k) (ha : ∀ i, a i ^ 2 = 1) :
    Generators.Construction.quadraticSymplectic (k := k) ⟨-diagonal a, (isSymm_diagonal a).neg⟩ *
      GenerationSymplectic.Construction.upperSymplectic ⟨diagonal a, isSymm_diagonal a⟩ *
      Generators.Construction.quadraticSymplectic ⟨-diagonal a, (isSymm_diagonal a).neg⟩ =
        Generators.Construction.leviSymplectic (diagonalReflection a ha) * Generators.Construction.weylSymplectic k n := by
  have hD : diagonal a * diagonal a = 1 := (diagonalReflection a ha).val_inv
  apply Subtype.ext
  change _ * _ * _ = (Generators.Construction.leviSymplectic (diagonalReflection a ha)).val * (Generators.Construction.weylSymplectic k n).val
  have hlev : (Generators.Construction.leviSymplectic (diagonalReflection a ha)).val =
      Matrix.fromBlocks (diagonal a) 0 0 (diagonal a) := by
    rw [Generators.Construction.leviSymplectic_matrix, diagonalReflection_inv]
    simp [diagonalReflection]
  rw [hlev]
  change Matrix.fromBlocks 1 0 (-diagonal a) 1 * Matrix.fromBlocks 1 (diagonal a) 0 1 *
    Matrix.fromBlocks 1 0 (-diagonal a) 1 = Matrix.fromBlocks (diagonal a) 0 0 (diagonal a) *
      Matrix.fromBlocks 0 1 (-1) 0
  simp only [Matrix.fromBlocks_multiply, mul_one, one_mul, zero_mul, mul_zero,
    zero_add, add_zero, neg_mul, mul_neg, hD, add_neg_cancel, neg_add_cancel,
    neg_zero]

end

end OAI.RepresentationTheory.Weil.Local.ReflectionAlgebra.Construction
