import OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.MixedBasis
import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.ScalarEquiv
import OAI.NumberTheory.ArithmeticGroups.Lattices.SemilinearBasisCoordinates

/-! # Completion Map -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.CompletionMap.Construction

noncomputable section

/-! Specialization of the Minkowski Lie representation to an individual
archimedean completion, with compatible bases and adjoint actions. -/

open scoped Classical TensorProduct _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding

attribute [local instance] LieRing.ofAssociativeRing Minkowski.LieEq.Construction.mixedSpaceBaseAlgebra

def lieCompletionMap
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (v : InfinitePlace k) :
    MixedLattice.Construction.lieMixedModule G →ₛₗ[Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation v]
      Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k v.Completion)) where
  toFun A := ⟨A.val.map (Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation v),
    (Minkowski.LieEq.Construction.lieMixedModule_mem_iff_completions G hG A.val).mp A.property v⟩
  map_add' A B := Subtype.ext (Matrix.map_add _ (map_add _) _ _)
  map_smul' a A := by
    apply Subtype.ext
    ext i j : 1
    change Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation v (a * A.val i j) =
      Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation v a * Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation v (A.val i j)
    exact map_mul _ _ _

def lieCompletionBasis
    {k ι : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (v : InfinitePlace k)
    (b : Module.Basis ι k (Infinitesimal.Action.Construction.infinitesimalStabilizer G)) :
    Module.Basis ι v.Completion
      (Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k v.Completion))) :=
  (b.baseChange v.Completion).map (Infinitesimal.ScalarEquiv.Construction.infinitesimalScalarLinearEquiv G hG)

theorem lieCompletionMap_basis
    {k ι : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (v : InfinitePlace k)
    (b : Module.Basis ι k (Infinitesimal.Action.Construction.infinitesimalStabilizer G)) (i : ι) :
    lieCompletionMap G hG v (MixedBasis.Construction.lieMixedBasis G b i) = lieCompletionBasis G hG v b i := by
  apply Subtype.ext
  change (MixedBasis.Construction.lieMixedBasis G b i).val.map (Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation v) = _
  rw [MixedBasis.Construction.lieMixedBasis_coe, lieCompletionBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    Infinitesimal.ScalarEquiv.Construction.infinitesimalScalarLinearEquiv_coe, Infinitesimal.ScalarEquiv.Construction.infinitesimalScalarMap_tmul, one_smul]
  ext a c : 1
  exact Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation_embedding v ((b i).val a c)

def lieCompletionPoint
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)
    (g : Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G) (v : InfinitePlace k) :
    (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k v.Completion)).RationalPoints :=
  ⟨g.val v, by
    change g.val v ∈ G.subgroup v.Completion ((RingHom.id v.Completion).comp (algebraMap k v.Completion))
    simpa only [RingHom.id_comp] using g.property v⟩

theorem lieCompletionMap_adjoint
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (v : InfinitePlace k)
    (g : Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G) (A : MixedLattice.Construction.lieMixedModule G) :
    lieCompletionMap G hG v (MixedBasis.Construction.archimedeanLieAlgebraEquiv G hG g A) =
      ExponentialNormal.Construction.infinitesimalAdjoint (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k v.Completion))
        (lieCompletionPoint G g v) (lieCompletionMap G hG v A) := by
  apply Subtype.ext
  rw [ExponentialNormal.Construction.infinitesimalAdjoint_apply]
  change (Archimedean.LieMem.Construction.matrixUnitConjugationEquiv (Archimedean.LieMem.Construction.archimedeanLieUnit G g) A.val).map (Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation v) =
    (g.val v : Matrix (Fin n) (Fin n) v.Completion) * A.val.map (Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation v) *
      (((g.val v)⁻¹ : Algebraic.SL n v.Completion) : Matrix (Fin n) (Fin n) v.Completion)
  rw [Archimedean.LieMem.Construction.matrixUnitConjugationEquiv_apply]
  change (Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation v).mapMatrix
    ((Archimedean.Quotient.Construction.archimedeanMixedSL k n g.val : Matrix (Fin n) (Fin n) (mixedSpace k)) * A.val *
      (((Archimedean.Quotient.Construction.archimedeanMixedSL k n g.val)⁻¹ : Algebraic.SL n (mixedSpace k)) : Matrix (Fin n) (Fin n) (mixedSpace k))) =
    (g.val v : Matrix (Fin n) (Fin n) v.Completion) * A.val.map (Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation v) *
      (((g.val v)⁻¹ : Algebraic.SL n v.Completion) : Matrix (Fin n) (Fin n) v.Completion)
  exact Archimedean.LieMem.Construction.mixedCompletionEvaluation_conjugate v g.val A.val

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.CompletionMap.Construction
