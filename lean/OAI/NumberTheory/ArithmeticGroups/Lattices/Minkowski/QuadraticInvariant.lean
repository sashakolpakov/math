import OAI.NumberTheory.ArithmeticGroups.Lattices.QuadraticValue
import OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.Quotient

/-! # Quadratic Invariant -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.QuadraticInvariant.Construction

noncomputable section

/-! Fieldwise invariance of a bilinear form gives an invariant
mixed-space quadratic value for the real Minkowski representation. -/

open scoped Classical
open _root_.Matrix _root_.NumberField _root_.NumberField.mixedEmbedding

def mixedCompletionEvaluation {k : Type} [Field k] (v : InfinitePlace k) :
    mixedSpace k →+* v.Completion :=
  (Pi.evalRingHom (fun w : InfinitePlace k => w.Completion) v).comp
    (InfiniteAdeleRing.ringEquiv_mixedSpace k).symm.toRingHom

theorem mixedCompletionEvaluation_embedding {k : Type} [Field k]
    (v : InfinitePlace k) (a : k) :
    mixedCompletionEvaluation v (mixedEmbedding k a) = algebraMap k v.Completion a := by
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  change (InfiniteAdeleRing.ringEquiv_mixedSpace k).symm
    (InfiniteAdeleRing.ringEquiv_mixedSpace k (algebraMap k (InfiniteAdeleRing k) a)) v = _
  rw [RingEquiv.symm_apply_apply]
  rfl

theorem mixedCompletionEvaluation_matrix {k : Type} [Field k] {n : ℕ}
    (v : InfinitePlace k) (g : Archimedean.ExteriorAction.Construction.FullArchimedeanSL k n) :
    (mixedCompletionEvaluation v).mapMatrix
        (Archimedean.Quotient.Construction.archimedeanMixedSL k n g : Matrix (Fin n) (Fin n) (mixedSpace k)) =
      (g v : Matrix (Fin n) (Fin n) v.Completion) := by
  ext i j : 1
  change (InfiniteAdeleRing.ringEquiv_mixedSpace k).symm
    (InfiniteAdeleRing.ringEquiv_mixedSpace k (fun w => g w i j)) v = g v i j
  exact congrFun ((InfiniteAdeleRing.ringEquiv_mixedSpace k).symm_apply_apply
    (show InfiniteAdeleRing k from fun w => g w i j)) v

theorem archimedean_mixed_congruence_invariant
    {k : Type} [Field k] {n : ℕ} (g : Archimedean.ExteriorAction.Construction.FullArchimedeanSL k n)
    (Q : Matrix (Fin n) (Fin n) k)
    (hQ : ∀ v : InfinitePlace k,
      (g v : Matrix (Fin n) (Fin n) v.Completion).transpose * Q.map (algebraMap k v.Completion) *
        (g v : Matrix (Fin n) (Fin n) v.Completion) = Q.map (algebraMap k v.Completion)) :
    (Archimedean.Quotient.Construction.archimedeanMixedSL k n g : Matrix (Fin n) (Fin n) (mixedSpace k)).transpose *
        Q.map (mixedEmbedding k) * (Archimedean.Quotient.Construction.archimedeanMixedSL k n g : Matrix (Fin n) (Fin n) (mixedSpace k)) =
      Q.map (mixedEmbedding k) := by
  ext i j : 1
  apply (InfiniteAdeleRing.ringEquiv_mixedSpace k).symm.injective
  funext v
  let ev := mixedCompletionEvaluation v
  have heQ : ev.mapMatrix (Q.map (mixedEmbedding k)) = Q.map (algebraMap k v.Completion) := by
    ext a b : 1
    exact mixedCompletionEvaluation_embedding v (Q a b)
  have heB := mixedCompletionEvaluation_matrix v g
  have heT : ev.mapMatrix
      (Archimedean.Quotient.Construction.archimedeanMixedSL k n g : Matrix (Fin n) (Fin n) (mixedSpace k)).transpose =
        (g v : Matrix (Fin n) (Fin n) v.Completion).transpose :=
    congrArg Matrix.transpose heB
  have he := hQ v
  rw [← heQ, ← heT, ← heB, ← map_mul, ← map_mul] at he
  exact congrArg (fun M => M i j) he

theorem minkowski_quadraticValue_invariant
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)
    (Q : Matrix (Fin n) (Fin n) k)
    (hQ : ∀ (K : Type) [Field K] (v : k →+* K) (g : G.Points v),
      (g.val : Matrix (Fin n) (Fin n) K).transpose * Q.map v *
        (g.val : Matrix (Fin n) (Fin n) K) = Q.map v)
    (g : G.ArchimedeanProduct Set.univ) (x : Fin n → mixedSpace k) :
    QuadraticValue.Construction.quadraticValue (Q.map (mixedEmbedding k))
        (Archimedean.Quotient.Construction.archimedeanRealRepresentation k n (Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G g).val x) =
      QuadraticValue.Construction.quadraticValue (Q.map (mixedEmbedding k)) x := by
  change QuadraticValue.Construction.quadraticValue (Q.map (mixedEmbedding k))
    ((Archimedean.Quotient.Construction.archimedeanMixedSL k n (Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G g).val :
      Matrix (Fin n) (Fin n) (mixedSpace k)).mulVec x) = _
  rw [QuadraticValue.Construction.quadraticValue_congruence]
  congr 1
  apply archimedean_mixed_congruence_invariant
  intro v
  exact hQ v.Completion (algebraMap k v.Completion) (g ⟨v, Set.mem_univ v⟩)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.QuadraticInvariant.Construction
