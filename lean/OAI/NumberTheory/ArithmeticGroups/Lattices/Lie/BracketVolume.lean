import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.KillingForm
import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.LieBracketUniformGap
import OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointVolume

/-! # Bracket Volume -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.BracketVolume.Construction

noncomputable section

/-! Every real automorphism of the Minkowski Lie bracket preserves its
nondegenerate Killing form and therefore has absolute determinant one. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding _root_.Module

theorem lieMixedAdjoint_bracket_automorphism_conj
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (b : Basis (Fin m) ℝ (MixedLattice.Construction.lieMixedSpan G))
    (g : Matrix.GeneralLinearGroup (Fin m) ℝ) (hg : g ∈ BracketStabilizer.Construction.lieBracketMatrixGroup G hG b)
    (A : MixedLattice.Construction.lieMixedSpan G) :
    (LatticeFrameAction.Construction.matrixFrameAction b g).conjAlgEquiv ℝ (Minkowski.AdjointOperator.Construction.lieMixedAdjoint G hG A) =
      Minkowski.AdjointOperator.Construction.lieMixedAdjoint G hG (LatticeFrameAction.Construction.matrixFrameAction b g A) := by
  have hp := (Integral.TensorStabilizer.Construction.mem_multilinearOperationStabilizer_iff b 2 (Minkowski.LieBracket.Construction.lieMixedBracketForm G hG) g).mp hg
  apply LinearMap.ext
  intro B
  have he := hp ![A, (LatticeFrameAction.Construction.matrixFrameAction b g).symm B]
  change LatticeFrameAction.Construction.matrixFrameAction b g (Minkowski.LieBracket.Construction.lieMixedBracket G hG A ((LatticeFrameAction.Construction.matrixFrameAction b g).symm B)) =
    Minkowski.LieBracket.Construction.lieMixedBracket G hG (LatticeFrameAction.Construction.matrixFrameAction b g A)
      (LatticeFrameAction.Construction.matrixFrameAction b g ((LatticeFrameAction.Construction.matrixFrameAction b g).symm B)) at he
  rw [LinearEquiv.apply_symm_apply] at he
  exact he

theorem lieMixedKillingForm_bracket_automorphism
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (b : Basis (Fin m) ℝ (MixedLattice.Construction.lieMixedSpan G))
    (g : Matrix.GeneralLinearGroup (Fin m) ℝ) (hg : g ∈ BracketStabilizer.Construction.lieBracketMatrixGroup G hG b)
    (A B : MixedLattice.Construction.lieMixedSpan G) :
    Minkowski.KillingForm.Construction.lieMixedKillingForm G hG (LatticeFrameAction.Construction.matrixFrameAction b g A) (LatticeFrameAction.Construction.matrixFrameAction b g B) =
      Minkowski.KillingForm.Construction.lieMixedKillingForm G hG A B := by
  change LinearMap.trace ℝ (MixedLattice.Construction.lieMixedSpan G)
      (Minkowski.AdjointOperator.Construction.lieMixedAdjoint G hG (LatticeFrameAction.Construction.matrixFrameAction b g A) * Minkowski.AdjointOperator.Construction.lieMixedAdjoint G hG (LatticeFrameAction.Construction.matrixFrameAction b g B)) =
    LinearMap.trace ℝ (MixedLattice.Construction.lieMixedSpan G) (Minkowski.AdjointOperator.Construction.lieMixedAdjoint G hG A * Minkowski.AdjointOperator.Construction.lieMixedAdjoint G hG B)
  rw [← lieMixedAdjoint_bracket_automorphism_conj G hG b g hg A,
    ← lieMixedAdjoint_bracket_automorphism_conj G hG b g hg B, ← map_mul, LinearMap.trace_map]

theorem lieBracketMatrixGroup_abs_determinant
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (b : Basis (Fin m) ℝ (MixedLattice.Construction.lieMixedSpan G))
    (g : Matrix.GeneralLinearGroup (Fin m) ℝ) (hg : g ∈ BracketStabilizer.Construction.lieBracketMatrixGroup G hG b) :
    |g.val.det| = 1 := by
  have he := AdjointVolume.Construction.bilinear_isometry_determinant_sq (Minkowski.KillingForm.Construction.lieMixedKillingForm G hG)
    (Minkowski.KillingForm.Construction.lieMixedKillingForm_nondegenerate G hG hsemi) (LatticeFrameAction.Construction.matrixFrameAction b g)
    (lieMixedKillingForm_bracket_automorphism G hG b g hg)
  rw [LatticeFrameAction.Construction.matrixFrameAction_det] at he
  nlinarith [sq_abs g.val.det, abs_nonneg g.val.det]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.BracketVolume.Construction
