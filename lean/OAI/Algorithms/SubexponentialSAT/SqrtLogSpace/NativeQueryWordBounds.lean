import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedFactorFields
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds

/-! The authentic factor specification inherits its row and clause bounds
from the actual physical formula, row-stream and width words. These are
length bounds, so they remain valid with leading zeros and repeated entries. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryWordBounds

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing
open LeafProgram LeafProgram.PreparedSource LeafParametersProgram

/-- Each stored selector term occupies exactly the fixed positive bit width. -/
theorem rowBits_length {m : ℕ} (b : ℕ) (terms : List (Fin m × ZMod 3)) :
    (HashScopeProgram.RawTable.rowBits b terms).length = b * terms.length := by
  induction terms with
  | nil => simp [HashScopeProgram.RawTable.rowBits]
  | cons a terms ih =>
    simp only [HashScopeProgram.RawTable.rowBits, List.map_cons, List.flatten_cons,
      List.length_append, HashInputProgram.Loop.word, fixedBits_length,
      List.length_cons] at *
    rw [Nat.mul_add, Nat.mul_one, ih, Nat.add_comm]

/-- An actual row, including repetitions and zero coefficients, is paid for
by its physical framed input stream. -/
theorem row_length_le_stream {m : ℕ} (b : ℕ) (hb : 0 < b)
    (rows : HashScopeProgram.RawTable.Rows m) (f : ℕ) (hf : f < rows.length) :
    rows[f].length ≤ (HashScopeProgram.RawTable.inputBits b rows).length := by
  have h := LeafScopeInputBounds.encoded_member_length id
    (rows.map (HashScopeProgram.RawTable.rowBits b))
    (HashScopeProgram.RawTable.rowBits b rows[f])
    (List.mem_map.mpr ⟨rows[f], List.getElem_mem hf, rfl⟩)
  have hmul : rows[f].length ≤ b * rows[f].length := by
    have hb' : 1 ≤ b := by omega
    simpa only [one_mul] using Nat.mul_le_mul_right rows[f].length hb'
  simp only [id_eq, rowBits_length] at h
  exact hmul.trans h

/-- Every original clause is bounded by its actual two-level formula bytes. -/
theorem source_clause_length {n : ℕ} (source : List (List (SAT.Literal (Fin n))))
    (ls : List (SAT.Literal (Fin n))) (hls : ls ∈ source) :
    ls.length ≤ (Encoding.encodeList id
      (HashInputProgram.Expansion.encodedClauses source)).length := by
  have h := Encoding.length_encodeList_lower
    (fun l => Encoding.encodeNat (Encoding.literalCode l)) ls
  have hm := LeafScopeInputBounds.encoded_member_length id
    (HashInputProgram.Expansion.encodedClauses source)
    (HashInputProgram.clausePayload ls) (List.mem_map.mpr ⟨ls,hls,rfl⟩)
  change ls.length+1 ≤ (HashInputProgram.clausePayload ls).length at h
  exact (by omega : ls.length ≤ (HashInputProgram.clausePayload ls).length).trans hm

/-- The optional marked clause has the same bound even for an absent mark. -/
theorem marked_clause_length {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A : ℕ)
    (hsource : ∀ ls ∈ q.source, ls.length ≤ A) : q.markedClause.length ≤ A := by
  unfold Factor.Spec.markedClause
  by_cases h : q.mark < q.source.length
  · simpa only [List.getElem?_eq_getElem h, Option.getD_some] using
      hsource q.source[q.mark] (List.getElem_mem h)
  · simp [List.getElem?_eq_none (Nat.le_of_not_gt h)]

/-- Integer lifting assigns a weight to each original clause without
changing its literal list. -/
theorem weighted_width {n : ℕ} (t d A : ℕ)
    (source : List (List (SAT.Literal (Fin n))))
    (hsource : ∀ ls ∈ source, ls.length ≤ A)
    (terms : List (Fin (HashInputProgram.Expansion.encodedClauses source).length × ZMod 3)) :
    ∀ w ∈ HashInputProgram.Expansion.weightedRow t d source terms,
      w.literals.length ≤ A := by
  intro w hw
  obtain ⟨a,_ha,rfl⟩ := List.mem_map.mp hw
  exact hsource _ (List.getElem_mem _)

/-- The only physical premises are the three immutable source words. -/
theorem spec_words {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (a : StructuredProgram.State 40 768) (A : ℕ)
    (hformula : a.stacks 700 = Encoding.encodeList id q.clauses)
    (hrows : a.stacks 701 = Encoding.encodeList id q.rawRows)
    (hwidth : (a.stacks 708).length = q.bitWidth)
    (h700 : (a.stacks 700).length ≤ A)
    (h701 : (a.stacks 701).length ≤ A)
    (h708 : (a.stacks 708).length ≤ A) :
    q.bitWidth ≤ A ∧
    (∀ f (hf : f < q.rows.length), q.rows[f].length ≤ A) ∧
    q.markedClause.length ≤ A ∧
    (∀ f (hf : f < q.rows.length),
      ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
        w.literals.length ≤ A) := by
  have hs : ∀ ls ∈ q.source, ls.length ≤ A := by
    intro ls hls
    apply (source_clause_length q.source ls hls).trans
    simpa only [hformula, Factor.Spec.clauses] using h700
  refine ⟨hwidth ▸ h708, ?_, marked_clause_length q A hs, ?_⟩
  · intro f hf
    apply (row_length_le_stream q.bitWidth q.bitWidthPositive q.rows f hf).trans
    have hraw : q.rawRows = q.rows.map (HashScopeProgram.RawTable.rowBits q.bitWidth) := by
      unfold Factor.Spec.rawRows HashScopeProgram.RawTable.rowBits
        HashInputProgram.Loop.rawInput
      simp only [List.reverse_reverse]
    change (Encoding.encodeList id
      (q.rows.map (HashScopeProgram.RawTable.rowBits q.bitWidth))).length ≤ A
    rw [← hraw, ← hrows]
    exact h701
  · intro f hf
    exact weighted_width q.p.t d A q.source hs q.rows[f]

section Produced
variable (s : LeafHeadSetupProgram.Native.Inputs)
    (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect s.height
      (LeafHeadSetupProgram.unary s.R) s.width words)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : s.Q < 3^(m.val 34)) (q : LeafQueryFrontend.Query) (hv : q.Valid)
    (J : ℕ) (hJ : 0 < J) (source : List (List (SAT.Literal (Fin s.n))))
    (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source)

local notation "spec" => nativeSpecOfInputs s m ht hd words hc M cache half e hp
  hfield q hv J hJ source hsource

/-- These are the row, marked-clause and width bounds for the genuine
produced ring and addressed native-input factor, with no new source service. -/
theorem produced_words (a : StructuredProgram.State 40 768) (A : ℕ)
    (ha : LeafProgram.Query.Sources q a)
    (h700 : (a.stacks 700).length ≤ A)
    (h701 : (a.stacks 701).length ≤ A)
    (h708 : (a.stacks 708).length ≤ A) :
    (spec).bitWidth ≤ A ∧
    (∀ f (hf : f < (spec).rows.length), (spec).rows[f].length ≤ A) ∧
    (spec).markedClause.length ≤ A ∧
    (∀ f (hf : f < (spec).rows.length),
      ∀ w ∈ HashInputProgram.Expansion.weightedRow (spec).p.t (m.val 34)
        (spec).source (spec).rows[f], w.literals.length ≤ A) := by
  apply spec_words (spec) a A _ _ _ h700 h701 h708
  · exact ha.formula.trans (congrArg (Encoding.encodeList id) hsource)
  · exact ha.rows.trans (nativeSpecOfInputs_rows s m ht hd words hc M cache half e hp
      hfield q hv J hJ source hsource).symm
  · exact congrArg List.length ha.width

/-- If the original CNF has width k, the same genuine weighted rows keep
that width; no tuple multiplicity or finite-ring coefficient changes it. -/
theorem produced_weighted_width (k : ℕ) (hk : ∀ ls ∈ source, ls.length ≤ k) :
    ∀ f (hf : f < (spec).rows.length),
      ∀ w ∈ HashInputProgram.Expansion.weightedRow (spec).p.t (m.val 34)
        (spec).source (spec).rows[f], w.literals.length ≤ k := by
  intro f hf
  exact weighted_width (spec).p.t (m.val 34) k source hk (spec).rows[f]

end Produced
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryWordBounds
