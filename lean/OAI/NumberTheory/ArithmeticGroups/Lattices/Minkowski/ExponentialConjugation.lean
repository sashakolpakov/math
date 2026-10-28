import OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointExponentialConjugation
import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.LieLocalExponential

/-! # Exponential Conjugation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.ExponentialConjugation.Construction

noncomputable section

/-! Intrinsic adjoint exponentials agree with conjugation by the
faithful Minkowski matrix exponential. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Operator
open _root_.NumberField _root_.NumberField.mixedEmbedding NormedSpace

local instance lieMixedSpan_normed_uniform_for_conjugation_exp
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    UniformSpace (Lie.MixedLattice.Construction.lieMixedSpan G) :=
  (inferInstance : NormedAddCommGroup (Lie.MixedLattice.Construction.lieMixedSpan G)).toUniformSpace

local instance lieMixedSpan_normed_topology_for_conjugation_exp
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    TopologicalSpace (Lie.MixedLattice.Construction.lieMixedSpan G) :=
  (inferInstance : NormedAddCommGroup (Lie.MixedLattice.Construction.lieMixedSpan G)).toUniformSpace.toTopologicalSpace

local instance lieMixedOperator_topologicalRing_for_conjugation_exp
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    IsTopologicalRing (Lie.MixedLattice.Construction.lieMixedSpan G →L[ℝ] Lie.MixedLattice.Construction.lieMixedSpan G) :=
  @NonUnitalSeminormedRing.toIsTopologicalRing _
    (inferInstance : NonUnitalSeminormedRing (Lie.MixedLattice.Construction.lieMixedSpan G →L[ℝ] Lie.MixedLattice.Construction.lieMixedSpan G))

def lieMixedMatrixInclusion
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    Lie.MixedLattice.Construction.lieMixedSpan G →L[ℝ] Matrix (Fin n) (Fin n) (mixedSpace k) :=
  (Lie.MixedLattice.Construction.lieMixedSpan G).subtype.toContinuousLinearMap

theorem lieMixed_adjoint_exp_conjugation
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (A X : Lie.MixedLattice.Construction.lieMixedSpan G) :
    (exp (LieTangent.Construction.lieMixedContinuousBracket G hG A) X).val =
      exp A.val * X.val * exp (-A.val) := by
  let : CompleteSpace (Lie.MixedLattice.Construction.lieMixedSpan G) := FiniteDimensional.complete ℝ (Lie.MixedLattice.Construction.lieMixedSpan G)
  let : CompleteSpace (Matrix (Fin n) (Fin n) (mixedSpace k)) :=
    FiniteDimensional.complete ℝ (Matrix (Fin n) (Fin n) (mixedSpace k))
  exact AdjointExponentialConjugation.Construction.exp_represented_commutator (lieMixedMatrixInclusion G)
    (LieTangent.Construction.lieMixedContinuousBracket G hG A) A.val (fun _ => rfl) X

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.ExponentialConjugation.Construction
