import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.LieBracket
import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.TensorStabilizer
import OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointMatrixTopology

/-! # Bracket Stabilizer -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.BracketStabilizer.Construction

noncomputable section

/-! The archimedean adjoint image lies in the bracket stabilizer, whose
image in the integral lattice quotient is closed. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding _root_.Module

def lieBracketMatrixGroup
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (b : Basis (Fin m) ℝ (MixedLattice.Construction.lieMixedSpan G)) : Subgroup (Matrix.GeneralLinearGroup (Fin m) ℝ) :=
  Integral.TensorStabilizer.Construction.multilinearOperationStabilizer b 2 (Minkowski.LieBracket.Construction.lieMixedBracketForm G hG)

theorem archimedeanLieMatrixCoordinates_mem_bracket_group
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (b : Basis (Fin m) ℝ (MixedLattice.Construction.lieMixedSpan G)) (g : Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G) :
    AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates G hG b g ∈ lieBracketMatrixGroup G hG b := by
  apply (Integral.TensorStabilizer.Construction.mem_multilinearOperationStabilizer_iff b 2 (Minkowski.LieBracket.Construction.lieMixedBracketForm G hG) _).mpr
  intro v
  rw [AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates_action]
  exact Minkowski.LieBracket.Construction.archimedeanLieRepresentation_bracket G hG g (v 0) (v 1)

local instance lieMixedLatticeInSpan_normed_discrete_for_bracket
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    @DiscreteTopology (MixedLattice.Construction.lieMixedLatticeInSpan G)
      (@instTopologicalSpaceSubtype (MixedLattice.Construction.lieMixedSpan G) _
        (inferInstance : NormedAddCommGroup (MixedLattice.Construction.lieMixedSpan G)).toUniformSpace.toTopologicalSpace) :=
  MixedLattice.Construction.lieMixedLatticeInSpan_discrete G

theorem lieBracketMatrixGroup_quotient_image_closed
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (b : Basis (Fin m) ℝ (MixedLattice.Construction.lieMixedSpan G))
    (hb : Submodule.span ℤ (Set.range b) = MixedLattice.Construction.lieMixedLatticeInSpan G) :
    let Γ := SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b) (MixedLattice.Construction.lieMixedLatticeInSpan G)
    IsClosed ((QuotientGroup.mk : Matrix.GeneralLinearGroup (Fin m) ℝ →
      Matrix.GeneralLinearGroup (Fin m) ℝ ⧸ Γ) ''
        (lieBracketMatrixGroup G hG b : Set (Matrix.GeneralLinearGroup (Fin m) ℝ))) := by
  apply Integral.TensorStabilizer.Construction.multilinearOperationStabilizer_quotient_image_closed (MixedLattice.Construction.lieMixedLatticeInSpan G) b hb
  intro t
  apply Minkowski.LieBracket.Construction.lieMixedBracket_integral G hG
  · rw [← hb]
    exact Submodule.subset_span (Set.mem_range_self (t 0))
  · rw [← hb]
    exact Submodule.subset_span (Set.mem_range_self (t 1))

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.BracketStabilizer.Construction
