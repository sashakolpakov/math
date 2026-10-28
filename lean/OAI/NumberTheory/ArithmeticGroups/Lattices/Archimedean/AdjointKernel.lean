import OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointKernelFieldFinite
import OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.Lie

/-! # Adjoint Kernel -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.AdjointKernel.Construction

noncomputable section

/-! The actual archimedean adjoint representation has finite kernel. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding _root_.MvPolynomial

theorem archimedean_adjoint_kernel_commutes_base
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (g : ExteriorAction.Construction.fullArchimedeanMatrixGroup G) (hg : LieMem.Construction.archimedeanLieRepresentation G hG g = 1)
    (v : InfinitePlace k) (A : Matrix (Fin n) (Fin n) k) (hA : A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    (g.val v : Matrix (Fin n) (Fin n) v.Completion) * A.map (algebraMap k v.Completion) =
      A.map (algebraMap k v.Completion) * (g.val v : Matrix (Fin n) (Fin n) v.Completion) := by
  let a : Infinitesimal.Action.Construction.infinitesimalStabilizer G := ⟨A, hA⟩
  have he := congrArg (fun e : Lie.MixedLattice.Construction.lieMixedSpan G ≃ₗ[ℝ] Lie.MixedLattice.Construction.lieMixedSpan G =>
    (e (Lie.Construction.lieMixedSpanRationalMap G a)).val) hg
  change LieMem.Construction.matrixUnitConjugationEquiv (LieMem.Construction.archimedeanLieUnit G g) (Lie.MixedLattice.Construction.lieMixedEmbedding G a) =
    Lie.MixedLattice.Construction.lieMixedEmbedding G a at he
  rw [LieMem.Construction.matrixUnitConjugationEquiv_apply] at he
  have hv := congrArg (Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation v).mapMatrix he
  change (Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation v).mapMatrix
    ((Quotient.Construction.archimedeanMixedSL k n g.val : Matrix (Fin n) (Fin n) (mixedSpace k)) * Lie.MixedLattice.Construction.lieMixedEmbedding G a *
      (((Quotient.Construction.archimedeanMixedSL k n g.val)⁻¹ : Algebraic.SL n (mixedSpace k)) : Matrix (Fin n) (Fin n) (mixedSpace k))) =
      (Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation v).mapMatrix (Lie.MixedLattice.Construction.lieMixedEmbedding G a) at hv
  rw [LieMem.Construction.mixedCompletionEvaluation_conjugate] at hv
  have hbase : (Lie.MixedLattice.Construction.lieMixedEmbedding G a).map (Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation v) =
      A.map (algebraMap k v.Completion) := by
    ext i j : 1
    exact Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation_embedding v (A i j)
  change (g.val v : Matrix (Fin n) (Fin n) v.Completion) *
      (Lie.MixedLattice.Construction.lieMixedEmbedding G a).map (Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation v) *
        (((g.val v)⁻¹ : Algebraic.SL n v.Completion) : Matrix (Fin n) (Fin n) v.Completion) =
      (Lie.MixedLattice.Construction.lieMixedEmbedding G a).map (Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation v) at hv
  rw [hbase] at hv
  have hm := congrArg (fun M : Matrix (Fin n) (Fin n) v.Completion =>
    M * (g.val v : Matrix (Fin n) (Fin n) v.Completion)) hv
  simpa only [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one] using hm

theorem archimedeanLieRepresentation_kernel_finite
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (hsemi : G.IsSemisimple) :
    Finite (LieMem.Construction.archimedeanLieRepresentation G hG).ker := by
  let Z (v : InfinitePlace k) := zeroLocus v.Completion (Infinitesimal.CentralizerEquations.Construction.infinitesimalCentralizerIdeal G)
  let : ∀ v, Finite (Z v) := fun v =>
    (AdjointKernelFieldFinite.Construction.finite_infinitesimalCentralizer_locus (K := v.Completion) G hG hsemi).to_subtype
  let f : (LieMem.Construction.archimedeanLieRepresentation G hG).ker → ∀ v, Z v := fun g v =>
    ⟨fun ij => g.val.val v ij.1 ij.2, by
      apply Infinitesimal.CentralizerEquations.Construction.point_mem_infinitesimalCentralizer_zeroLocus G
        (⟨g.val.val v, g.val.property v⟩ : G.Points (algebraMap k v.Completion))
      exact archimedean_adjoint_kernel_commutes_base G hG g.val g.property v⟩
  apply Finite.of_injective f
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  funext v
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  exact congrArg (fun z : ∀ v, Z v => (z v).val (i, j)) he

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.AdjointKernel.Construction
