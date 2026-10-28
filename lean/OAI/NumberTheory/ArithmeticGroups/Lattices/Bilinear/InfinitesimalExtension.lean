import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.RationalForm
import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Action

/-! # Infinitesimal Extension -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.InfinitesimalExtension.Construction

noncomputable section

/-! Infinitesimal invariance of a bilinear form persists under scalar
extension and controls derivatives at every group point. -/

open scoped Classical
open _root_.Matrix

attribute [local instance] LieRing.ofAssociativeRing

theorem bilinear_infinitesimal_invariant_baseChange
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (Q : Matrix (Fin n) (Fin n) k)
    (hQ : ∀ A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G, A.transpose * Q + Q * A = 0) :
    ∀ A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)),
      A.transpose * Q.map (algebraMap k K) + Q.map (algebraMap k K) * A = 0 := by
  let f := Compact.RationalForm.Construction.bilinearFormInfinitesimalMap (Q.map (algebraMap k K))
  have hle : (Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K))).toSubmodule ≤
      f.ker := by
    rw [Infinitesimal.TangentExtension.Construction.infinitesimalStabilizer_eq_span_base G hG]
    apply Submodule.span_le.mpr
    rintro _ ⟨A, hA, rfl⟩
    change InvariantSystem.Construction.bilinearLieVariation (A.map (algebraMap k K)) (Q.map (algebraMap k K)) = 0
    rw [InvariantSystem.Construction.bilinearLieVariation_coefficient_map]
    have hz : InvariantSystem.Construction.bilinearLieVariation A Q = 0 := hQ A hA
    rw [hz]
    exact map_zero (algebraMap k K).mapMatrix
  exact fun A hA => hle hA

theorem congruence_derivative_eq_conjugate_variation
    {k : Type} [Field k] {n : ℕ} (g : Algebraic.SL n k) (A Q : Matrix (Fin n) (Fin n) k) :
    ((g : Matrix (Fin n) (Fin n) k) * A).transpose * Q * (g : Matrix (Fin n) (Fin n) k) +
      (g : Matrix (Fin n) (Fin n) k).transpose * Q * ((g : Matrix (Fin n) (Fin n) k) * A) =
    (g : Matrix (Fin n) (Fin n) k).transpose *
      (((g : Matrix (Fin n) (Fin n) k) * A * (g⁻¹ : Algebraic.SL n k)).transpose * Q +
        Q * ((g : Matrix (Fin n) (Fin n) k) * A * (g⁻¹ : Algebraic.SL n k))) *
      (g : Matrix (Fin n) (Fin n) k) := by
  have hgi : (g⁻¹ : Algebraic.SL n k) * (g : Matrix (Fin n) (Fin n) k) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hgt : (g : Matrix (Fin n) (Fin n) k).transpose *
      ((g⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k).transpose = 1 := by
    rw [← Matrix.transpose_mul, hgi, Matrix.transpose_one]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_mul]
  congr 1
  · simp only [← Matrix.mul_assoc, hgt, Matrix.one_mul]
  · simp only [Matrix.mul_assoc, hgi, Matrix.mul_one]

theorem bilinear_infinitesimal_invariant_derivative_zero
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)
    (Q : Matrix (Fin n) (Fin n) k)
    (hQ : ∀ A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G, A.transpose * Q + Q * A = 0)
    (g : G.RationalPoints) {A : Matrix (Fin n) (Fin n) k}
    (hA : A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    ((g.val : Matrix (Fin n) (Fin n) k) * A).transpose * Q * (g.val : Matrix (Fin n) (Fin n) k) +
      (g.val : Matrix (Fin n) (Fin n) k).transpose * Q *
        ((g.val : Matrix (Fin n) (Fin n) k) * A) = 0 := by
  rw [congruence_derivative_eq_conjugate_variation,
    hQ _ (Infinitesimal.Action.Construction.infinitesimalStabilizer_conjugation G g hA), Matrix.mul_zero, Matrix.zero_mul]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.InfinitesimalExtension.Construction
