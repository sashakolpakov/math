import OAI.NumberTheory.ArithmeticGroups.Lattices.CyclicWordBasis
import OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.WordMinors
import OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantFrameMinors
import OAI.NumberTheory.ArithmeticGroups.Lattices.NonzeroFrameMinor

/-! # Cyclic Invariant Minor -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.CyclicInvariantMinor.Construction

noncomputable section

/-! Every nonzero vector has a nonzero invariant word minor, using
only words of bounded length in any spanning family of Lie matrices. -/

open scoped Classical
open _root_.Module

theorem exists_invariant_cyclic_word_frame
    {k ι : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n)
    (A : ι → Matrix (Fin n) (Fin n) k)
    (hA : ∀ T ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G, T ∈ Submodule.span k (Set.range A))
    (x : Fin n → k) (hx : x ≠ 0) :
    ∃ (r : ℕ) (w : Fin r → Finite.WordMinors.Construction.boundedWord ι n), 0 < r ∧ r ≤ n ∧
      LinearIndependent k (fun j => Finite.WordMinors.Construction.matrixWordAction A (w j).toList x) ∧
      ∀ T ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G,
        ∀ y ∈ Submodule.span k (Set.range (fun j => Finite.WordMinors.Construction.matrixWordAction A (w j).toList x)),
          T.mulVec y ∈ Submodule.span k (Set.range (fun j => Finite.WordMinors.Construction.matrixWordAction A (w j).toList x)) := by
  let B : ι → Module.End k (Fin n → k) := fun i => Matrix.toLin' (A i)
  obtain ⟨r, v, hr, hv, hlin, hspan⟩ := CyclicWordBasis.Construction.exists_cyclicWord_basis B x
  have hrn : r ≤ n := by simpa using hr
  have hrpos : 0 < r := by
    by_contra h
    have hr0 : r = 0 := Nat.eq_zero_of_not_pos h
    subst r
    have hself := BoundedCyclicWords.Construction.self_mem_cyclicWordSpan B x (finrank k (Fin n → k))
    rw [← hspan] at hself
    exact hx (by simpa using hself)
  have hvn : ∀ i, (v i).length ≤ n := fun i => by simpa using hv i
  choose w hw using fun i => Finite.WordMinors.Construction.boundedWord.exists_toList (v i) (hvn i)
  have hword : (fun j => Finite.WordMinors.Construction.matrixWordAction A (w j).toList x) =
      (fun j => BoundedCyclicWords.Construction.operatorWord B (v j) x) := by
    funext j
    rw [hw j, Finite.WordMinors.Construction.matrixWordAction_eq_operatorWord]
  refine ⟨r, w, hrpos, hrn, hword.symm ▸ hlin, ?_⟩
  rw [hword, hspan]
  intro T hT y hy
  apply CyclicWordBounds.Construction.cyclicWordSpan_invariant_of_mem_operator_span B x (Matrix.toLin' T) _ y hy
  have hm := Submodule.mem_map_of_mem (f := (Matrix.toLin' :
    Matrix (Fin n) (Fin n) k ≃ₗ[k] Module.End k (Fin n → k)).toLinearMap) (hA T hT)
  rw [Submodule.map_span, ← Set.range_comp] at hm
  exact hm

theorem exists_nonzero_invariant_word_minor
    {k ι : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hs : G.IsSemisimple)
    (A : ι → Matrix (Fin n) (Fin n) k)
    (hA : ∀ T ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G, T ∈ Submodule.span k (Set.range A))
    (x : Fin n → k) (hx : x ≠ 0) :
    ∃ q : Finite.WordMinors.Construction.boundedWordMinorIndex ι n n, Finite.WordMinors.Construction.boundedWordMinor q A x ≠ 0 ∧
      ∀ (K : Type) [Field K] (σ : k →+* K) (g : G.Points σ),
        (Matrix.of (fun i j => (g.val : Matrix (Fin n) (Fin n) K).mulVec
          (fun a => σ (Finite.WordMinors.Construction.matrixWordAction A ((q.2.1 j).toList) x a)) (q.2.2 i))).det =
            σ (Finite.WordMinors.Construction.boundedWordMinor q A x) := by
  obtain ⟨r, w, hr, hrn, hlin, hW⟩ := exists_invariant_cyclic_word_frame G A hA x hx
  let v := fun j => Finite.WordMinors.Construction.matrixWordAction A (w j).toList x
  let W := Submodule.span k (Set.range v)
  let b : Basis (Fin r) k W := Basis.span hlin
  let U : Matrix (Fin n) (Fin r) k := Matrix.of (fun i j => v j i)
  obtain ⟨rows, hrows⟩ := NonzeroFrameMinor.Construction.exists_nonzero_frame_minor U hlin
  let q : Finite.WordMinors.Construction.boundedWordMinorIndex ι n n := ⟨⟨⟨r, Nat.lt_succ_of_le hrn⟩, hr⟩, w, rows⟩
  refine ⟨q, hrows, ?_⟩
  intro K _ σ g
  have he := InvariantFrameMinors.Construction.group_preserves_invariant_basis_minors G hG hs W hW b rows σ g
  have hframe : Matrix.of (fun i j => (b j).val i) = U := by
    ext i j : 1
    exact congrFun (Basis.coe_span_apply hlin j) i
  rw [hframe] at he
  exact he

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.CyclicInvariantMinor.Construction
