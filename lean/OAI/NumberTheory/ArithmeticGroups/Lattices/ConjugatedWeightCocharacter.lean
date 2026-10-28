import OAI.NumberTheory.ArithmeticGroups.Lattices.ConjugatedWeightCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.AnisotropicIntegerWeights

/-! # Conjugated Weight Cocharacter -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ConjugatedWeightCocharacter.Construction

noncomputable section

/-! Integration of conjugated integer diagonal infinitesimal matrices
to cocharacters, and exclusion of these matrices by anisotropy. -/

open scoped Classical
open _root_.Matrix

def conjugatedInfinitesimalCocharacter
    {k : Type} [Field k] [CharZero k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)
    (b : Algebraic.SL n k) (w : Fin n → ℤ)
    (hw : (b : Matrix (Fin n) (Fin n) k) * Matrix.diagonal (fun i => (w i : k)) *
      ((b⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G) : G.Cocharacter where
  hom K _ v :=
    ((MulAut.conj (Matrix.SpecialLinearGroup.map v b)).toMonoidHom.comp
      (DiagonalWeightIntegration.Construction.diagonalWeightHom K w (ConjugatedWeightCoordinates.Construction.conjugated_integer_diagonal_trace_zero_weights G b w hw))).codRestrict
      (G.subgroup K v) (fun t => ConjugatedWeightCoordinates.Construction.conjugate_diagonalWeightSL_mem_group G b w
        (ConjugatedWeightCoordinates.Construction.conjugated_integer_diagonal_trace_zero_weights G b w hw) hw v t)
  coordinates := ConjugatedWeightCoordinates.Construction.conjugatedWeightCoordinates b w
  coordinate_eq K _ v t i j := by
    have he := congrArg (fun M => M i j) (ConjugatedWeightCoordinates.Construction.evaluate_conjugatedWeightCoordinates v b w
      (ConjugatedWeightCoordinates.Construction.conjugated_integer_diagonal_trace_zero_weights G b w hw) t)
    exact he.symm

theorem anisotropic_conjugated_integer_weights_zero
    {k : Type} [Field k] [CharZero k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (haniso : Algebraic.IsAnisotropic G) (b : Algebraic.SL G.dimension k) (w : Fin G.dimension → ℤ)
    (hw : (b : Matrix (Fin G.dimension) (Fin G.dimension) k) * Matrix.diagonal (fun i => (w i : k)) *
      ((b⁻¹ : Algebraic.SL G.dimension k) : Matrix (Fin G.dimension) (Fin G.dimension) k) ∈
        Infinitesimal.Action.Construction.infinitesimalStabilizer G.matrixGroup) : w = 0 := by
  let c := conjugatedInfinitesimalCocharacter G.matrixGroup b w hw
  let t : kˣ := Units.mk0 2 (by norm_num)
  let hsum := ConjugatedWeightCoordinates.Construction.conjugated_integer_diagonal_trace_zero_weights G.matrixGroup b w hw
  let B := Matrix.SpecialLinearGroup.map (RingHom.id k) b
  have he := DFunLike.congr_fun (haniso c k (RingHom.id k)) t
  have heSL := congrArg (fun g : G.matrixGroup.RationalPoints => g.val) he
  change MulAut.conj B (DiagonalWeightIntegration.Construction.diagonalWeightSL k w hsum t) = 1 at heSL
  have hd : DiagonalWeightIntegration.Construction.diagonalWeightSL k w hsum t = 1 :=
    (MulAut.conj B).injective (heSL.trans (map_one (MulAut.conj B)).symm)
  funext i
  have hi := congrArg (fun g : Algebraic.SL G.dimension k => g i i) hd
  change (Matrix.diagonal (fun j => ((t ^ w j : kˣ) : k))) i i =
    (1 : Matrix (Fin G.dimension) (Fin G.dimension) k) i i at hi
  simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Units.val_zpow_eq_zpow_val] at hi
  exact (AnisotropicIntegerWeights.Construction.charZero_two_zpow_eq_one_iff (k := k) (w i)).mp hi

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ConjugatedWeightCocharacter.Construction
