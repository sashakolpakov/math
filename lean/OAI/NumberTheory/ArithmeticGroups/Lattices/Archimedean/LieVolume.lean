import OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.CompletionMap
import OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointVolume

/-! # Lie Volume -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.LieVolume.Construction

noncomputable section

/-! The real Minkowski adjoint representation preserves volume. Its
determinant has square one at every completion and after restriction
of scalars to the reals. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding

attribute [local instance] LieRing.ofAssociativeRing Minkowski.LieEq.Construction.mixedSpaceBaseAlgebra

theorem archimedeanLie_matrix_completion
    {k ι : Type} [Field k] [NumberField k] [Fintype ι] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (b : Module.Basis ι k (Infinitesimal.Action.Construction.infinitesimalStabilizer G))
    (g : ExteriorAction.Construction.fullArchimedeanMatrixGroup G) (v : InfinitePlace k) :
    (LinearMap.toMatrix (Lie.MixedBasis.Construction.lieMixedBasis G b) (Lie.MixedBasis.Construction.lieMixedBasis G b)
      (Lie.MixedBasis.Construction.archimedeanLieAlgebraEquiv G hG g).toLinearMap).map (Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation v) =
      LinearMap.toMatrix (Lie.CompletionMap.Construction.lieCompletionBasis G hG v b) (Lie.CompletionMap.Construction.lieCompletionBasis G hG v b)
        (ExponentialNormal.Construction.infinitesimalAdjoint (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k v.Completion))
          (Lie.CompletionMap.Construction.lieCompletionPoint G g v)).toLinearMap := by
  apply SemilinearBasisCoordinates.Construction.semilinear_intertwining_matrix (Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation v)
    (Lie.MixedBasis.Construction.lieMixedBasis G b) (Lie.CompletionMap.Construction.lieCompletionBasis G hG v b) (Lie.CompletionMap.Construction.lieCompletionMap G hG v)
    (Lie.CompletionMap.Construction.lieCompletionMap_basis G hG v b)
  exact Lie.CompletionMap.Construction.lieCompletionMap_adjoint G hG v g

theorem archimedeanLie_determinant_completion
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (g : ExteriorAction.Construction.fullArchimedeanMatrixGroup G) (v : InfinitePlace k) :
    Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation v (LinearMap.det (Lie.MixedBasis.Construction.archimedeanLieAlgebraEquiv G hG g).toLinearMap) =
      LinearMap.det (ExponentialNormal.Construction.infinitesimalAdjoint (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k v.Completion))
        (Lie.CompletionMap.Construction.lieCompletionPoint G g v)).toLinearMap := by
  let b := Module.finBasis k (Infinitesimal.Action.Construction.infinitesimalStabilizer G)
  apply SemilinearBasisCoordinates.Construction.semilinear_intertwining_determinant (Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation v)
    (Lie.MixedBasis.Construction.lieMixedBasis G b) (Lie.CompletionMap.Construction.lieCompletionBasis G hG v b) (Lie.CompletionMap.Construction.lieCompletionMap G hG v)
    (Lie.CompletionMap.Construction.lieCompletionMap_basis G hG v b)
  exact Lie.CompletionMap.Construction.lieCompletionMap_adjoint G hG v g

theorem archimedeanLieAlgebraEquiv_determinant_sq
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (g : ExteriorAction.Construction.fullArchimedeanMatrixGroup G) :
    LinearMap.det (Lie.MixedBasis.Construction.archimedeanLieAlgebraEquiv G hG g).toLinearMap ^ 2 = 1 := by
  apply Minkowski.LieEq.Construction.mixedCompletionEvaluation_jointly_injective
  intro v
  let H := BaseChange.Construction.matrixGroupBaseChange G (algebraMap k v.Completion)
  let : LieAlgebra.IsKilling v.Completion (Infinitesimal.Action.Construction.infinitesimalStabilizer H) :=
    KillingScalarExtension.Construction.infinitesimal_baseChange_isKilling G hG hsemi
  rw [map_pow, map_one, archimedeanLie_determinant_completion]
  exact AdjointVolume.Construction.killing_LieEquiv_determinant_sq _

theorem archimedeanLieRepresentation_norm_determinant
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (g : ExteriorAction.Construction.fullArchimedeanMatrixGroup G) :
    ‖LinearMap.det (LieMem.Construction.archimedeanLieRepresentation G hG g).toLinearMap‖ = 1 := by
  let b := Module.finBasis k (Infinitesimal.Action.Construction.infinitesimalStabilizer G)
  let : Module.Free (mixedSpace k) (Lie.MixedLattice.Construction.lieMixedModule G) := Module.Free.of_basis (Lie.MixedBasis.Construction.lieMixedBasis G b)
  have hs : LinearMap.det (LieMem.Construction.archimedeanLieEquiv G hG g).toLinearMap ^ 2 = 1 := by
    rw [← Lie.MixedBasis.Construction.archimedeanLieAlgebraEquiv_restrictScalars]
    change LinearMap.det ((Lie.MixedBasis.Construction.archimedeanLieAlgebraEquiv G hG g).toLinearMap.restrictScalars ℝ) ^ 2 = 1
    rw [LinearMap.det_restrictScalars, ← map_pow, archimedeanLieAlgebraEquiv_determinant_sq G hG hsemi, map_one]
  have h := congrArg (fun x : ℝ => ‖x‖) hs
  rw [norm_pow, norm_one] at h
  have hnonneg := norm_nonneg (LinearMap.det (LieMem.Construction.archimedeanLieEquiv G hG g).toLinearMap)
  change ‖LinearMap.det (LieMem.Construction.archimedeanLieEquiv G hG g).toLinearMap‖ = 1
  nlinarith

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.LieVolume.Construction
