import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramGeneratedWords
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramGraphWord

namespace OAI.Algorithms

/-! A proof-only typed view of the binary characters produced by the fixed tuple machine.
The order need not agree with any other finite enumeration. No decoding or
choice operation is executed by the bit program. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

private theorem list_lift {α β : Type*} (f : α → β) (ys : List β)
    (h : ∀ y ∈ ys, ∃ x, f x = y) : ∃ xs : List α, xs.map f = ys := by
  induction ys with
  | nil => exact ⟨[],rfl⟩
  | cons y ys ih =>
      obtain ⟨x,hx⟩ := h y (by simp)
      obtain ⟨xs,hxs⟩ := ih (fun z hz => h z (by simp [hz]))
      exact ⟨x :: xs, by simp [hx,hxs]⟩

theorem generated_characters_typed (D : ℕ) :
    ∃ values : List (Fin D → ZMod 2),
      values.map (fun x => scalarFrames (List.ofFn x)) = framedCandidates 2 D ∧
      values.length = 2 ^ D ∧ (∀ x, x ∈ values) := by
  obtain ⟨values,hvalues⟩ := list_lift (fun x : Fin D → ZMod 2 =>
    scalarFrames (List.ofFn x)) (framedCandidates 2 D) (by
      intro bits hb
      obtain ⟨v,hv⟩ := (framedCandidates_sound bits).mp hb
      exact ⟨v, by simpa only [framedVector_eq_scalarFrames] using hv⟩)
  refine ⟨values,hvalues,?_,?_⟩
  · have h := congrArg List.length hvalues
    simpa using h
  · intro x
    have hx : scalarFrames (List.ofFn x) ∈
        values.map (fun x => scalarFrames (List.ofFn x)) := by
      rw [hvalues, ← framedVector_eq_scalarFrames]
      exact framedCandidates_complete x
    obtain ⟨v,hv,hvx⟩ := List.mem_map.mp hx
    have heq : v = x := by
      apply SubexpTupleRefinement.encodeTuple_injective (framedScalarCode 2)
      change framedVector v = framedVector x
      simpa only [← framedVector_eq_scalarFrames] using hvx
    simpa [heq] using hv

theorem generated_graphs_typed (t D : ℕ) :
    ∃ values : List (Fin t → Fin D → ZMod 2),
      values.map matrixFrames = framedCandidates 2 (t * D) ∧
      values.length = 2 ^ (t * D) ∧ (∀ Q, Q ∈ values) := by
  obtain ⟨words,hw,hlen,hcomplete⟩ := generated_characters_typed (t * D)
  refine ⟨words.map (expandMatrix (rows := t) (cols := D)), ?_, ?_, ?_⟩
  · rw [List.map_map]
    have heq : (fun Q : Fin t → Fin D → ZMod 2 => matrixFrames Q) ∘
        (expandMatrix (p := 2) (rows := t) (cols := D)) =
        (fun x : Fin (t * D) → ZMod 2 => scalarFrames (List.ofFn x)) := by
      funext x
      change matrixFrames (expandMatrix (rows := t) (cols := D) x) = scalarFrames (List.ofFn x)
      rw [← framedMatrix_eq_matrixFrames]
      simp only [ framedMatrix, flatten_expand,
        framedVector_eq_scalarFrames]
    rw [heq,hw]
  · simpa using hlen
  · intro Q
    exact List.mem_map.mpr ⟨flattenMatrix Q,hcomplete _,expand_flatten Q⟩


/-- The exact finite character scan accepts precisely the integer Walsh
predicate. This is a semantic lemma for the separately implemented bit scan. -/
theorem complete_characters_reject_false_iff {r D : ℕ}
    (values : List (Cayley.Cube r)) (complete : ∀ a, a ∈ values)
    (s : Fin D → Cayley.Cube r) (q : ℕ) :
    values.any (fun a => decide (graphWordRejects s a q)) = false ↔
      WalshExistence.Good q s := by
  rw [WalshExistence.good_iff_parity_checks]
  constructor
  · intro h a ha
    have hx := List.any_eq_false.mp h a (complete a)
    have hn : ¬ graphWordRejects s a q := by simpa using hx
    by_contra hf
    exact hn ⟨ha,hf⟩
  · intro h
    apply List.any_eq_false.mpr
    intro a _
    have hn : ¬ graphWordRejects s a q := by
      rintro ⟨ha,hbad⟩
      exact hbad (h a ha)
    simpa using hn

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
