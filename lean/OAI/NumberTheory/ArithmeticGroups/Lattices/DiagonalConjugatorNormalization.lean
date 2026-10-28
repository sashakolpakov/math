import OAI.NumberTheory.ArithmeticGroups.Lattices.ConjugatedWeightCocharacter
import OAI.NumberTheory.ArithmeticGroups.Lattices.EigenbasisMatrixSpectral

/-! # Diagonal Conjugator Normalization -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.DiagonalConjugatorNormalization.Construction

noncomputable section

/-! An invertible diagonalizing change of basis can be normalized to
determinant one without changing its diagonal conjugates. -/

open scoped Classical
open _root_.Matrix

theorem diagonal_conjugator_normalization
    {k : Type} [Field k] {n : ℕ} [Nonempty (Fin n)]
    (g : Matrix.GeneralLinearGroup (Fin n) k) :
    ∃ b : Algebraic.SL n k, ∀ w : Fin n → k,
      (b : Matrix (Fin n) (Fin n) k) * Matrix.diagonal w *
        ((b⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) =
      g.val * Matrix.diagonal w * (g⁻¹).val := by
  let j : Fin n := Classical.arbitrary _
  let u := g.det
  let d : Matrix.GeneralLinearGroup (Fin n) k :=
    ⟨Matrix.diagonal (fun i => if i = j then (u⁻¹).val else 1),
      Matrix.diagonal (fun i => if i = j then u.val else 1), by
        rw [Matrix.diagonal_mul_diagonal]
        ext i l : 1
        by_cases hij : i = j <;> simp [hij, Matrix.diagonal_apply, Matrix.one_apply], by
        rw [Matrix.diagonal_mul_diagonal]
        ext i l : 1
        by_cases hij : i = j <;> simp [hij, Matrix.diagonal_apply, Matrix.one_apply]⟩
  have hdetd : d.val.det = (u⁻¹).val := by
    change (Matrix.diagonal (fun i : Fin n => if i = j then (u⁻¹).val else 1)).det = _
    simp [Matrix.det_diagonal]
  have hdet : (g * d).val.det = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hdetd]
    exact u.mul_inv
  let b : Algebraic.SL n k := ⟨(g * d).val, hdet⟩
  have hb : Matrix.SpecialLinearGroup.toGL b = g * d := Units.ext rfl
  have hbi : ((b⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) = ((g * d)⁻¹).val := by
    have h := congrArg (fun x : Matrix.GeneralLinearGroup (Fin n) k => (x⁻¹).val) hb
    simpa only [← map_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using h
  refine ⟨b, fun w => ?_⟩
  have hcomm : d.val * Matrix.diagonal w = Matrix.diagonal w * d.val := by
    change Matrix.diagonal _ * Matrix.diagonal w = Matrix.diagonal w * Matrix.diagonal _
    simp only [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  change (g * d).val * Matrix.diagonal w * ((b⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) = _
  rw [hbi, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  calc
    g.val * d.val * Matrix.diagonal w * ((d⁻¹).val * (g⁻¹).val) =
      g.val * (d.val * Matrix.diagonal w * (d⁻¹).val) * (g⁻¹).val := by simp only [mul_assoc]
    _ = g.val * Matrix.diagonal w * (g⁻¹).val := by
      rw [hcomm, mul_assoc (Matrix.diagonal w), d.mul_inv, mul_one]

theorem anisotropic_unit_conjugated_integer_weights_zero
    {k : Type} [Field k] [CharZero k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (haniso : Algebraic.IsAnisotropic G) (g : Matrix.GeneralLinearGroup (Fin G.dimension) k)
    (w : Fin G.dimension → ℤ)
    (hw : g.val * Matrix.diagonal (fun i => (w i : k)) * (g⁻¹).val ∈
      Infinitesimal.Action.Construction.infinitesimalStabilizer G.matrixGroup) : w = 0 := by
  cases isEmpty_or_nonempty (Fin G.dimension) with
  | inl h => exact Subsingleton.elim _ _
  | inr h =>
    obtain ⟨b, hb⟩ := diagonal_conjugator_normalization g
    apply ConjugatedWeightCocharacter.Construction.anisotropic_conjugated_integer_weights_zero G haniso b w
    rwa [hb]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.DiagonalConjugatorNormalization.Construction
