import OAI.NumberTheory.ArithmeticGroups.Lattices.CyclicInvariantMinor
import OAI.NumberTheory.ArithmeticGroups.Lattices.WordMinorNaturality
import OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.LieMem

/-! # Word Minor -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.WordMinor.Construction

noncomputable section

/-! Invariant nonzero word minors persist under the faithful Minkowski
action and simultaneous conjugation of the Lie operators. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding

theorem archimedean_invariant_frame_minor
    {k : Type} [Field k] {n r : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)
    (U : Matrix (Fin n) (Fin r) k) (rows : Fin r → Fin n)
    (hU : ∀ (K : Type) [Field K] (σ : k →+* K) (g : G.Points σ),
      (((g.val : Matrix (Fin n) (Fin n) K) * U.map σ).submatrix rows id).det =
        σ (U.submatrix rows id).det)
    (g : Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G) :
    (((Archimedean.LieMem.Construction.archimedeanLieUnit G g).val * U.map (mixedEmbedding k)).submatrix rows id).det =
      mixedEmbedding k (U.submatrix rows id).det := by
  apply LieEq.Construction.mixedCompletionEvaluation_jointly_injective
  intro v
  rw [RingHom.map_det, QuadraticInvariant.Construction.mixedCompletionEvaluation_embedding]
  have heG : ((Archimedean.LieMem.Construction.archimedeanLieUnit G g).val).map (QuadraticInvariant.Construction.mixedCompletionEvaluation v) =
      (g.val v : Matrix (Fin n) (Fin n) v.Completion) :=
    QuadraticInvariant.Construction.mixedCompletionEvaluation_matrix v g.val
  have heU : (U.map (mixedEmbedding k)).map (QuadraticInvariant.Construction.mixedCompletionEvaluation v) =
      U.map (algebraMap k v.Completion) := by
    ext i j : 1
    exact QuadraticInvariant.Construction.mixedCompletionEvaluation_embedding v (U i j)
  have he : (QuadraticInvariant.Construction.mixedCompletionEvaluation v).mapMatrix
      (((Archimedean.LieMem.Construction.archimedeanLieUnit G g).val * U.map (mixedEmbedding k)).submatrix rows id) =
        (((g.val v : Matrix (Fin n) (Fin n) v.Completion) *
          U.map (algebraMap k v.Completion)).submatrix rows id) := by
    change ((((Archimedean.LieMem.Construction.archimedeanLieUnit G g).val * U.map (mixedEmbedding k)).map
      (QuadraticInvariant.Construction.mixedCompletionEvaluation v)).submatrix rows id) = _
    rw [Matrix.map_mul, heG, heU]
  rw [he]
  exact hU v.Completion (algebraMap k v.Completion) ⟨g.val v, g.property v⟩

theorem exists_nonzero_minkowski_word_minor
    {k ι : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hs : G.IsSemisimple)
    (A : ι → Matrix (Fin n) (Fin n) k)
    (hA : ∀ T ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G, T ∈ Submodule.span k (Set.range A))
    (x : Fin n → k) (hx : x ≠ 0) (g : Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G) :
    ∃ q : Finite.WordMinors.Construction.boundedWordMinorIndex ι n n, Finite.WordMinors.Construction.boundedWordMinor q A x ≠ 0 ∧
      Finite.WordMinors.Construction.boundedWordMinor q
        (fun i => (Archimedean.LieMem.Construction.archimedeanLieUnit G g).val * (A i).map (mixedEmbedding k) *
          ((Archimedean.LieMem.Construction.archimedeanLieUnit G g)⁻¹).val)
        ((Archimedean.LieMem.Construction.archimedeanLieUnit G g).val.mulVec (fun i => mixedEmbedding k (x i))) =
          mixedEmbedding k (Finite.WordMinors.Construction.boundedWordMinor q A x) := by
  obtain ⟨q, hq, hfixed⟩ := CyclicInvariantMinor.Construction.exists_nonzero_invariant_word_minor G hG hs A hA x hx
  let U : Matrix (Fin n) (Fin q.1.val.val) k :=
    Matrix.of (fun i j => Finite.WordMinors.Construction.matrixWordAction A ((q.2.1 j).toList) x i)
  have he := archimedean_invariant_frame_minor G U q.2.2 hfixed g
  refine ⟨q, hq, ?_⟩
  change _ = mixedEmbedding k (U.submatrix q.2.2 id).det
  rw [← he]
  apply congrArg Matrix.det
  ext i j : 1
  change Finite.WordMinors.Construction.matrixWordAction _ ((q.2.1 j).toList) _ (q.2.2 i) = _
  rw [← WordMinorNaturality.Construction.matrixWordAction_conjugate, ← WordMinorNaturality.Construction.matrixWordAction_map]
  rfl

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.WordMinor.Construction
