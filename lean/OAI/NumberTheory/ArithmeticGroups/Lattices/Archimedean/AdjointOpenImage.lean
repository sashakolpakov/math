import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.ArchimedeanAdjointExponential
import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousFrameOperator
import OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.BracketStabilizer
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Adjoint Open Image -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.AdjointOpenImage.Construction

noncomputable section

/-! The actual archimedean adjoint image is an open subgroup of the
real Lie-automorphism group. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise _root_.Topology
open _root_.NumberField _root_.NumberField.mixedEmbedding _root_.Module Filter

def archimedeanLieBracketRepresentation
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (b : Basis (Fin m) ℝ (Lie.MixedLattice.Construction.lieMixedSpan G)) :
    ExteriorAction.Construction.fullArchimedeanMatrixGroup G →* Lie.BracketStabilizer.Construction.lieBracketMatrixGroup G hG b :=
  (AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates G hG b).codRestrict _
    (Lie.BracketStabilizer.Construction.archimedeanLieMatrixCoordinates_mem_bracket_group G hG b)

theorem continuous_archimedeanLieBracketRepresentation
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (b : Basis (Fin m) ℝ (Lie.MixedLattice.Construction.lieMixedSpan G)) :
    Continuous (archimedeanLieBracketRepresentation G hG b) :=
  (AdjointMatrixTopology.Construction.continuous_archimedeanLieMatrixCoordinates G hG b).subtype_mk _

theorem archimedean_adjoint_image_open
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (b : Basis (Fin m) ℝ (Lie.MixedLattice.Construction.lieMixedSpan G)) :
    IsOpen ((archimedeanLieBracketRepresentation G hG b).range :
      Set (Lie.BracketStabilizer.Construction.lieBracketMatrixGroup G hG b)) := by
  let H := Lie.BracketStabilizer.Construction.lieBracketMatrixGroup G hG b
  let ρ := archimedeanLieBracketRepresentation G hG b
  let F : H → (Lie.MixedLattice.Construction.lieMixedSpan G →L[ℝ] Lie.MixedLattice.Construction.lieMixedSpan G) :=
    fun T => ContinuousFrameOperator.Construction.continuousFrameOperator b T.val
  have hF : Continuous F :=
    (ContinuousFrameOperator.Construction.continuous_continuousFrameOperator b).comp continuous_subtype_val
  have hF1 : F 1 = 1 := ContinuousFrameOperator.Construction.continuousFrameOperator_one b
  have ht : Tendsto F (𝓝 (1 : H)) (𝓝 1) := by
    simpa only [hF1] using hF.tendsto (1 : H)
  apply ρ.range.isOpen_of_mem_nhds (g := 1)
  filter_upwards [ht.eventually (Minkowski.LieLocalExponential.Construction.lieMixed_near_identity_is_exponential G hG hsemi)] with T hT
  have hTB : ∀ X Y, F T (Minkowski.LieBracket.Construction.lieMixedBracket G hG X Y) =
      Minkowski.LieBracket.Construction.lieMixedBracket G hG (F T X) (F T Y) := by
    intro X Y
    exact (Integral.TensorStabilizer.Construction.mem_multilinearOperationStabilizer_iff b 2 (Minkowski.LieBracket.Construction.lieMixedBracketForm G hG) T.val).mp
      T.property ![X, Y]
  obtain ⟨A, hA⟩ := hT hTB
  obtain ⟨g, hg⟩ := Minkowski.ArchimedeanAdjointExponential.Construction.archimedean_adjoint_exponential_in_image G hG A
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply ContinuousFrameOperator.Construction.continuousFrameOperator_injective b
  apply ContinuousLinearMap.ext
  intro X
  have hgX := DFunLike.congr_fun hg X
  have hAX := DFunLike.congr_fun hA X
  change LatticeFrameAction.Construction.matrixFrameAction b (AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates G hG b g) X =
    LatticeFrameAction.Construction.matrixFrameAction b T.val X
  rw [AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates_action]
  exact hgX.trans hAX

theorem archimedean_adjoint_image_closed
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (b : Basis (Fin m) ℝ (Lie.MixedLattice.Construction.lieMixedSpan G)) :
    IsClosed ((archimedeanLieBracketRepresentation G hG b).range :
      Set (Lie.BracketStabilizer.Construction.lieBracketMatrixGroup G hG b)) :=
  (archimedeanLieBracketRepresentation G hG b).range.isClosed_of_isOpen
    (archimedean_adjoint_image_open G hG hsemi b)

theorem archimedeanLieMatrixCoordinates_range_closed
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (b : Basis (Fin m) ℝ (Lie.MixedLattice.Construction.lieMixedSpan G)) :
    IsClosed (Set.range (AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates G hG b)) := by
  have hH : IsClosed (Lie.BracketStabilizer.Construction.lieBracketMatrixGroup G hG b : Set (Matrix.GeneralLinearGroup (Fin m) ℝ)) :=
    Integral.TensorStabilizer.Construction.multilinearOperationStabilizer_closed b 2 (Minkowski.LieBracket.Construction.lieMixedBracketForm G hG)
  have hc := hH.isClosedEmbedding_subtypeVal.isClosedMap _
    (archimedean_adjoint_image_closed G hG hsemi b)
  change IsClosed (Subtype.val '' Set.range (archimedeanLieBracketRepresentation G hG b)) at hc
  rw [← Set.range_comp] at hc
  exact hc

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.AdjointOpenImage.Construction
