import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCodeConstruct
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Enumerators

/-!
# Sparse rows from the candidates actually selected by the search

The construction below consumes the selected shifts and local matrix explicitly. Its
proofs need their checked Walsh and distance properties, not identity with the old
materialized search's selected candidates. The finite list of final rows is polynomial
size and can be retained; lists of all candidates and all test words cannot.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeProgram

open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode
open scoped BigOperators

def selectedMatrix (m B : ℕ) (hm : 0 < m) (hB : 0 < B)
    (shifts : Fin (degree m B) → Cayley.Cube (dimension m B))
    (Q : CheckMatrix (Fin (localRows m B)) (Fin (degree m B))) :
    CheckMatrix (Fin (totalRows m B)) (Fin m) :=
  fun r c => (Cayley.graph shifts).matrix Q (rowEquiv m B r)
    (columnEmbedding m B hm hB c)

def selectedRows (m B : ℕ) (hm : 0 < m) (hB : 0 < B)
    (shifts : Fin (degree m B) → Cayley.Cube (dimension m B))
    (Q : CheckMatrix (Fin (localRows m B)) (Fin (degree m B))) : List (Fin m → F3) :=
  List.ofFn (fun r => selectedMatrix m B hm hB shifts Q r)

/-- Positive parameter values ensure that a checked graph and local code exist.
The actual streaming search must use completeness to select such candidates. -/
theorem candidates_exist {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    (∃ shifts : Fin (degree m B) → Cayley.Cube (dimension m B),
      WalshExistence.Good (gapDenom m B) shifts) ∧
    (∃ Q : CheckMatrix (Fin (localRows m B)) (Fin (degree m B)),
      HasDistance Q (degree m B / (100 * B * logSize m) + 1)) := by
  constructor
  · by_cases hr : dimension m B = 0
    · refine ⟨fun _ => 0, ?_⟩
      intro a ha
      apply False.elim (ha ?_)
      funext i
      have hi := i.isLt
      omega
    · obtain ⟨shifts, hs⟩ := WalshExistence.exists_smallWalsh _ _ _
        (gapDenom_pos m hB) (walsh_degree_bound hm hB hr)
      exact ⟨shifts, (WalshExistence.good_iff_smallWalsh (gapDenom_pos m hB) shifts).mpr hs⟩
  · exact LocalCode.exists_local_code_log_bound _ _ _ _ hB (logSize_pos m)
      (degree_le_power m B) (localRows_lower hB)

theorem selectedMatrix_distance {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (shifts : Fin (degree m B) → Cayley.Cube (dimension m B))
    (Q : CheckMatrix (Fin (localRows m B)) (Fin (degree m B)))
    (hgraph : WalshExistence.Good (gapDenom m B) shifts)
    (hlocal : HasDistance Q (degree m B / (100 * B * logSize m) + 1)) :
    HasRelativeDistance (selectedMatrix m B hm hB shifts Q)
      (1 / (distanceDenom m B : ℝ)) := by
  have hmix := Cayley.hasMixing_of_smallWalsh shifts (1 / (gapDenom m B : ℝ))
    (by positivity)
    ((WalshExistence.good_iff_smallWalsh (gapDenom_pos m hB) shifts).mp hgraph)
  have hdist := LocalCode.relative_of_log_distance hB (logSize_pos m) Q hlocal
  have hglobal := (Cayley.graph shifts).matrix_relativeDistance
    Fintype.card_pos (by simpa using degree_pos hm hB)
    (by positivity : (0 : ℝ) ≤ 1 / (100 * (B : ℝ) * logSize m)) hdist hmix
  rw [relative_fraction m hB] at hglobal
  have hshort := relativeDistance_shorten _ (columnEmbedding m B hm hB)
    (by positivity : (0 : ℝ) ≤ 1 / (distanceDenom m B : ℝ)) hglobal
  intro w hw hw0
  apply hshort w ?_ hw0
  intro r
  obtain ⟨i, rfl⟩ := (rowEquiv m B).surjective r
  exact hw i

@[simp] theorem selectedRows_length {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (shifts : Fin (degree m B) → Cayley.Cube (dimension m B))
    (Q : CheckMatrix (Fin (localRows m B)) (Fin (degree m B))) :
    (selectedRows m B hm hB shifts Q).length = totalRows m B := by
  simp only [selectedRows, List.length_ofFn]

theorem selectedRows_length_le {n m B : ℕ} (hn : 0 < n) (hm : 0 < m) (hB : 0 < B)
    (hmb : m ≤ n * B)
    (shifts : Fin (degree m B) → Cayley.Cube (dimension m B))
    (Q : CheckMatrix (Fin (localRows m B)) (Fin (degree m B))) :
    (selectedRows m B hm hB shifts Q).length ≤ 3 * n := by
  rw [selectedRows_length]
  exact totalRows_le hn hm hB hmb

theorem selectedMatrix_row_support {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (shifts : Fin (degree m B) → Cayley.Cube (dimension m B))
    (Q : CheckMatrix (Fin (localRows m B)) (Fin (degree m B)))
    (r : Fin (totalRows m B)) :
    weight (selectedMatrix m B hm hB shifts Q r) ≤ degreeBound m B := by
  have hshort := rowSupport_shorten_card_le ((Cayley.graph shifts).matrix Q)
    (columnEmbedding m B hm hB) (rowEquiv m B r)
  have hfull := (Cayley.graph shifts).matrix_rowSupport_card_le Q (rowEquiv m B r)
  exact (hshort.trans (by simpa using hfull)).trans (degree_le_bound m B)

theorem selectedRows_kernel_bound {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (shifts : Fin (degree m B) → Cayley.Cube (dimension m B))
    (Q : CheckMatrix (Fin (localRows m B)) (Fin (degree m B)))
    (hgraph : WalshExistence.Good (gapDenom m B) shifts)
    (hlocal : HasDistance Q (degree m B / (100 * B * logSize m) + 1))
    (w : Fin m → F3)
    (hw : ∀ r ∈ selectedRows m B hm hB shifts Q, (∑ c, r c * w c) = 0)
    (hw0 : w ≠ 0) : m ≤ distanceDenom m B * weight w := by
  have hcode : IsCodeword (selectedMatrix m B hm hB shifts Q) w := by
    intro r
    exact hw _ (List.mem_ofFn.mpr ⟨r, rfl⟩)
  simpa using relativeDistance_integer (distanceDenom_pos m hB)
    (selectedMatrix_distance hm hB shifts Q hgraph hlocal) w hcode hw0

/-- Dense serialization of the final selected code is polynomial even without
compressing sparse rows. This concerns only the retained result, not the search. -/
theorem selectedMatrix_encoding_length_le {n m B : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hB : 0 < B) (hmb : m ≤ n * B)
    (shifts : Fin (degree m B) → Cayley.Cube (dimension m B))
    (Q : CheckMatrix (Fin (localRows m B)) (Fin (degree m B))) :
    (CodeSearchProgram.matrixFrames
      (fun r c => selectedMatrix m B hm hB shifts Q r c)).length ≤
      15 * n * m := by
  rw [CodeSearchProgram.matrixFrames_ternary_length]
  have hrows := totalRows_le hn hm hB hmb
  have hmul := Nat.mul_le_mul_right m hrows
  nlinarith

theorem selectedLocal_encoding_length_le (m B : ℕ)
    (Q : CheckMatrix (Fin (localRows m B)) (Fin (degree m B))) :
    (CodeSearchProgram.matrixFrames (fun r c => Q r c)).length ≤
      5 * (m + 1) * m := by
  rw [CodeSearchProgram.matrixFrames_ternary_length]
  have hd := degree_le m B
  have hr : localRows m B ≤ m + 1 := by
    unfold localRows
    have := Nat.div_le_self (degree m B) (8 * B)
    omega
  have hmul := Nat.mul_le_mul hr hd
  nlinarith

theorem selectedGraph_encoding_length_le {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (shifts : Fin (degree m B) → Cayley.Cube (dimension m B)) :
    (CodeSearchProgram.matrixFrames shifts).length ≤ 5 * m * (m + 1) := by
  rw [CodeSearchProgram.matrixFrames_binary_length]
  have hd := degree_le m B
  have hr := dimension_lt_logSize hm hB
  have hl := Nat.log_le_self 2 m
  unfold logSize at hr
  have hmul := Nat.mul_le_mul hd (show dimension m B ≤ m + 1 by omega)
  nlinarith

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeProgram

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

/-- A proof-only predicate on the odometer rank. The native callback computes
this predicate by conversion and the arithmetic checks; it is never an oracle. -/
noncomputable def rejectedRank {p d : ℕ} [Fact p.Prime]
    (reject : (Fin d → ZMod p) → Prop) (rank : ℕ) : Bool := by
  classical
  exact decide (∃ x, CounterPrograms.value (CodeCandidates.fieldWords x).flatten = rank ∧ reject x)

theorem rejectedRank_field {p d : ℕ} [Fact p.Prime]
    (reject : (Fin d → ZMod p) → Prop) [DecidablePred reject] (x : Fin d → ZMod p) :
    rejectedRank reject (CounterPrograms.value (CodeCandidates.fieldWords x).flatten) =
      decide (reject x) := by
  classical
  unfold rejectedRank
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨y, hy, hr⟩
    have heq : y = x := CodeCandidates.fieldWords_injective
      (ExecCNFTupleEnumeration.tuple_eq_of_shape_value (by simp) hy)
    simpa [heq] using hr
  · intro hx
    exact ⟨x, rfl, hx⟩

theorem tupleBits_eq (xs : List (Bool × Bool)) :
    CodeCandidates.tupleBits xs = Encoding.encodeList id (xs.map CodeCandidates.digitBits) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [CodeCandidates.tupleBits, Encoding.encodeList] at ih ⊢; exact ih

private theorem rejectedRank_invalid {p d : ℕ} [Fact p.Prime]
    (reject : (Fin d → ZMod p) → Prop) (words : List (List Bool))
    (hshape : words.map List.length = List.replicate d (SubexpEnumerationPayload.scalarWidth p))
    (hinvalid : ∀ x : Fin d → ZMod p, words ≠ CodeCandidates.fieldWords x) :
    rejectedRank reject (CounterPrograms.value words.flatten) = false := by
  classical
  apply decide_eq_false (p := ∃ x : Fin d → ZMod p,
    CounterPrograms.value (CodeCandidates.fieldWords x).flatten = CounterPrograms.value words.flatten ∧
      reject x)
  rintro ⟨x, hx, _⟩
  exact hinvalid x (ExecCNFTupleEnumeration.tuple_eq_of_shape_value
    (hshape.trans (CodeCandidates.fieldWords_shape x).symm) hx.symm)

/-- Every width-two local-word candidate, including the invalid digits, has an
actual bounded callback execution. Only the persistent OR latch changes. -/
theorem local_stream_body {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (d : ℕ) (words : List (List Bool)) (hshape : words.map List.length = List.replicate D 2)
    (a : ScanState) (b : Bool)
    (he : WorkEmpty (projectState id localStreamStacks a))
    (hm : a.stacks 18 = matrixFrames Q) (ht : a.stacks 19 = List.replicate t true)
    (hd : a.stacks 20 = List.replicate d true)
    (hpayload : a.stacks 22 = []) (htmp : a.stacks 23 = [])
    (hcounter : a.stacks 24 = Encoding.encodeList id words)
    (hlatch : a.stacks 25 = [b]) (hcopy : a.stacks 27 = []) :
    ∃ steps out, steps ≤ callbackBudget t D d + 68 * D + 24 ∧
      Eval localStreamBody steps a out ∧
      out.stacks = Function.update a.stacks 25
        [b || rejectedRank (fun x => wordRejects Q x d) (CounterPrograms.value words.flatten)] := by
  obtain ⟨xs, hlen, hwords⟩ := CodeCandidates.pairs_of_shape words D hshape
  have hc : a.stacks 24 = CodeCandidates.tupleBits xs := by
    rw [tupleBits_eq, hwords]
    exact hcounter
  subst D
  cases hv : xs.any (CodeCandidates.invalidDigit true) with
  | false =>
      obtain ⟨x, hx⟩ := CodeCandidates.ternary_digits_sound xs hv
      obtain ⟨steps, out, hn, hrun, hout⟩ := local_stream_body_valid Q x d xs hx hv
        a b he hm ht hd hpayload htmp hc hlatch hcopy
      refine ⟨steps, out, hn, hrun, ?_⟩
      rw [← hwords, hx, rejectedRank_field]
      exact hout
  | true =>
      have hrejected : rejectedRank (fun x => wordRejects Q x d)
          (CounterPrograms.value words.flatten) = false := by
        apply rejectedRank_invalid
        · have hw : SubexpEnumerationPayload.scalarWidth 3 = 2 := by
            norm_num [SubexpEnumerationPayload.scalarWidth]
          simpa only [hw] using hshape
        · intro x hx
          have hvalid := CodeCandidates.ternary_field_valid xs x (hwords.trans hx)
          rw [hv] at hvalid
          contradiction
      obtain ⟨out, hrun, hout⟩ := invalid_conversion_eval true 24 27 22 23
        (.seq (.call (ProgramLinking.liftProgram callbackProgram id localStreamStacks))
          (latchReject 25)) (by decide) (by decide) (by decide) (by decide)
        xs a hc hcopy hpayload htmp hv
      refine ⟨68 * xs.length + 20, out, by omega, hrun, ?_⟩
      rw [hrejected, Bool.or_false, hout, ← hlatch, Function.update_eq_self]

/-- The binary graph domain is checked in the same bounded-memory scan; padded
high-bit candidates are charged and physically discarded. -/
theorem graph_stream_body {D r : ℕ} (s : Fin D → Cayley.Cube r)
    (q : ℕ) (qbits Dbits : List Bool)
    (hqv : BinaryArithmetic.toNat qbits = q) (hDv : BinaryArithmetic.toNat Dbits = D)
    (words : List (List Bool)) (hshape : words.map List.length = List.replicate r 2)
    (a : ScanState) (b : Bool)
    (he : GraphWorkEmpty (projectState id graphStreamStacks a))
    (hm : a.stacks 29 = matrixFrames s) (ht : a.stacks 30 = List.replicate D true)
    (hq : a.stacks 31 = qbits) (hD : a.stacks 32 = Dbits)
    (hpayload : a.stacks 34 = []) (htmp : a.stacks 35 = [])
    (hcounter : a.stacks 36 = Encoding.encodeList id words)
    (hlatch : a.stacks 37 = [b]) (hcopy : a.stacks 39 = []) :
    ∃ steps out, steps ≤ graphCallbackBudget D r qbits.length Dbits.length + 68 * r + 24 ∧
      Eval graphStreamBody steps a out ∧
      out.stacks = Function.update a.stacks 37
        [b || rejectedRank (fun x => graphWordRejects s x q) (CounterPrograms.value words.flatten)] := by
  obtain ⟨xs, hlen, hwords⟩ := CodeCandidates.pairs_of_shape words r hshape
  have hc : a.stacks 36 = CodeCandidates.tupleBits xs := by
    rw [tupleBits_eq, hwords]
    exact hcounter
  subst r
  cases hv : xs.any (CodeCandidates.invalidDigit false) with
  | false =>
      obtain ⟨x, hx⟩ := CodeCandidates.binary_digits_sound xs hv
      obtain ⟨steps, out, hn, hrun, hout⟩ := graph_stream_body_valid s x q qbits Dbits hqv hDv
        xs hx hv a b he hm ht hq hD hpayload htmp hc hlatch hcopy
      refine ⟨steps, out, hn, hrun, ?_⟩
      rw [← hwords, hx, rejectedRank_field]
      exact hout
  | true =>
      have hrejected : rejectedRank (fun x => graphWordRejects s x q)
          (CounterPrograms.value words.flatten) = false := by
        apply rejectedRank_invalid
        · have hw : SubexpEnumerationPayload.scalarWidth 2 = 2 := by
            norm_num [SubexpEnumerationPayload.scalarWidth]
          simpa only [hw] using hshape
        · intro x hx
          have hvalid := CodeCandidates.binary_field_valid xs x (hwords.trans hx)
          rw [hv] at hvalid
          contradiction
      obtain ⟨out, hrun, hout⟩ := invalid_conversion_eval false 36 39 34 35
        (.seq (.call (ProgramLinking.liftProgram graphCallbackProgram id graphStreamStacks))
          (latchReject 37)) (by decide) (by decide) (by decide) (by decide)
        xs a hc hcopy hpayload htmp hv
      refine ⟨68 * xs.length + 20, out, by omega, hrun, ?_⟩
      rw [hrejected, Bool.or_false, hout, ← hlatch, Function.update_eq_self]

/-- The iterator may alter its counter and scratch; one Boolean is the only
additional retained result. All other caller stacks have an exact frame. -/
structure RejectionFrame {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (latch : Fin S) (base a : State R S) : Prop where
  frame : ∀ i, i ≠ p.counter → i ≠ p.scratch → i ≠ latch → a.stacks i = base.stacks i
  latch_word : ∃ b : Bool, a.stacks latch = [b]

theorem rejectionFrame_stable {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (latch : Fin S) (hc : latch ≠ p.counter) (hs : latch ≠ p.scratch)
    (base : State R S) :
    CounterForPrograms.FrameStable p (fun _ => RejectionFrame p latch base) := by
  intro _ a b hab ha
  refine ⟨?_, ?_⟩
  · intro i hi hj hk
    exact (hab i hi hj).symm.trans (ha.1 i hi hj hk)
  · obtain ⟨bit, hbit⟩ := ha.2
    exact ⟨bit, (hab latch hc hs).symm.trans hbit⟩

theorem rejectionFrame_update {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (latch : Fin S) (base a out : State R S) (bit : Bool)
    (ha : RejectionFrame p latch base a)
    (hout : out.stacks = Function.update a.stacks latch [bit]) :
    RejectionFrame p latch base out := by
  refine ⟨?_, bit, ?_⟩
  · intro i hi hj hk
    rw [hout, Function.update_of_ne hk]
    exact ha.1 i hi hj hk
  · rw [hout, Function.update_self]

/-- Intermediate contract for an actual, fixed rejection body. The concrete
local and graph bodies below instantiate this by their native arithmetic traces. -/
structure RejectionBody {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (latch : Fin S) (body : Cmd R S) (dimension budget : ℕ)
    (base : State R S) (reject : ℕ → Bool) : Prop where
  run : ∀ words a, words.map List.length = List.replicate dimension 2 →
    RejectionFrame p latch base a → a.stacks p.counter = Encoding.encodeList id words →
    a.stacks p.scratch = [] →
    ∃ n out, n ≤ budget ∧ Eval body n a out ∧
      out.stacks = Function.update a.stacks latch
        [(a.stacks latch).headD false || reject (CounterPrograms.value words.flatten)]

theorem RejectionBody.bodySpec {R S : ℕ} {p : CounterForPrograms.Ports R S}
    {latch : Fin S} {body : Cmd R S} {dimension budget : ℕ}
    {base : State R S} {reject : ℕ → Bool}
    (h : RejectionBody p latch body dimension budget base reject)
    (hc : latch ≠ p.counter) (hs : latch ≠ p.scratch) :
    ExecCNFTupleEnumeration.BodySpec p body (List.replicate dimension 2)
      (RejectionFrame p latch base) budget := by
  intro words a hw ha hac has
  obtain ⟨n, out, hn, he, ho⟩ := h.run words a hw ha hac has
  refine ⟨n, out, hn, he, ?_, ?_, rejectionFrame_update p latch base a out _ ha ho⟩
  · rw [ho, Function.update_of_ne (Ne.symm hc)]
    exact hac
  · rw [ho, Function.update_of_ne (Ne.symm hs)]
    exact has

theorem RejectionBody.actual {R S : ℕ} {p : CounterForPrograms.Ports R S}
    {latch : Fin S} {body : Cmd R S} {dimension budget : ℕ}
    {base : State R S} {reject : ℕ → Bool}
    (h : RejectionBody p latch body dimension budget base reject)
    (words : List (List Bool)) (a out : State R S) (n : ℕ)
    (hw : words.map List.length = List.replicate dimension 2)
    (ha : RejectionFrame p latch base a)
    (hc : a.stacks p.counter = Encoding.encodeList id words)
    (hs : a.stacks p.scratch = []) (he : Eval body n a out) :
    n ≤ budget ∧ out.stacks = Function.update a.stacks latch
      [(a.stacks latch).headD false || reject (CounterPrograms.value words.flatten)] := by
  obtain ⟨m, b, hm, hb, hout⟩ := h.run words a hw ha hc hs
  have hnm := StreamResources.eval_steps_eq p.counter latch he hb
  have hob := Eval.final_unique p.counter he hb
  subst m
  subst b
  exact ⟨hm, hout⟩

private theorem rejection_fold (ranks : List ℕ) (reject : ℕ → Bool) (b : Bool) :
    ranks.foldl (fun word rank => [word.headD false || reject rank]) [b] =
      [b || ranks.any reject] := by
  induction ranks generalizing b with
  | nil => simp
  | cons rank ranks ih =>
      change ranks.foldl (fun word rank => [word.headD false || reject rank])
        [b || reject rank] = [b || (reject rank || ranks.any reject)]
      rw [ih, Bool.or_assoc]

/-- Full actual stream correctness and cost, including every padded candidate,
all losing checks, the terminal increment, initialization, and halt. -/
theorem rejection_scan_runs {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (latch : Fin S) (hc : latch ≠ p.counter) (hs : latch ≠ p.scratch)
    (body : Cmd R S) (dimension budget : ℕ) (reject : ℕ → Bool)
    (a : State R S) (b : Bool)
    (hbody : RejectionBody p latch body dimension budget a reject)
    (hcounter : a.stacks p.counter =
      Encoding.encodeList id (List.replicate dimension [false, false]))
    (hscratch : a.stacks p.scratch = []) (hlatch : a.stacks latch = [b]) :
    ∃ n out, n ≤ 4 ^ dimension * (budget + 42 * dimension + 12) + 3 ∧
      Trace (ExecCNFTupleEnumeration.program p body) n
        (a.withPC (some (ExecCNFTupleEnumeration.program p body).entry)) (out.withPC none) ∧
      RejectionFrame p latch a out ∧ out.stacks p.scratch = [] ∧
      out.stacks latch = [b || (List.range' 0 (4 ^ dimension)).any reject] := by
  let I := RejectionFrame p latch a
  have stable := rejectionFrame_stable p latch hc hs a
  have spec := hbody.bodySpec hc hs
  have hi : I a := ⟨fun _ _ _ _ => rfl, b, hlatch⟩
  obtain ⟨n, out, he, hv, ho, _, hscratchout, hn⟩ :=
    ExecCNFTupleEnumeration.enumerate_correct p body (List.replicate dimension 2) I budget
      stable spec (List.replicate dimension [false, false]) a (by simp) hi
      hcounter hscratch (ExecCNFTupleEnumeration.zero_tuple_value dimension 2)
  have hp : 2 ^ (List.replicate dimension [false, false]).flatten.length = 4 ^ dimension := by
    simp only [List.length_flatten, List.map_replicate, List.length_cons, List.length_nil,
      List.sum_replicate, smul_eq_mul]
    change 2 ^ (dimension * 2) = 4 ^ dimension
    rw [Nat.mul_comm dimension 2, pow_mul]
    norm_num
  have hlen : (Encoding.encodeList id (List.replicate dimension [false, false])).length =
      6 * dimension + 1 := by
    rw [Enumerators.encoded_shape_length (by simp :
      (List.replicate dimension [false, false]).map List.length = List.replicate dimension 2)]
    simp
    omega
  have hstart : I (ExecCNFTupleEnumeration.startResult p a) :=
    stable 0 a _ (fun _ _ _ => rfl) hi
  obtain ⟨_, hfold⟩ := hv.stack_fold_of_invariant latch hc hs
    (fun word rank => [word.headD false || reject rank])
    (fun state => I state ∧ state.stacks p.scratch = []) ⟨hstart, hscratch⟩
    (by
      intro words start finish steps hw hcounter' hrun hI
      have hactual := hbody.actual words start finish steps hw hI.1 hcounter' hI.2 hrun
      have hout := hactual.2
      refine ⟨⟨rejectionFrame_update p latch a start finish _ hI.1 hout, ?_⟩, ?_⟩
      · rw [hout, Function.update_of_ne (Ne.symm hs)]
        exact hI.2
      · rw [hout, Function.update_self])
    (by
      intro words state hI
      exact ⟨stable 0 state _ (ExecCNFTupleEnumeration.advanceResult_outside p state words) hI.1,
        ExecCNFTupleEnumeration.advanceResult_scratch p state words⟩)
  refine ⟨1 + n + 1, out, ?_, compiled_halt_trace he p.counter p.counter,
    ho, hscratchout, ?_⟩
  · rw [hp, hlen] at hn
    nlinarith
  · rw [ExecCNFTupleEnumeration.startResult_stacks, hlatch, rejection_fold, hp] at hfold
    exact hfold

/-- The local-code iterator contract is discharged by the concrete byte-level
checker for every current tuple and every retained caller frame. -/
theorem local_rejection_body {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (d : ℕ) (base : ScanState)
    (he : WorkEmpty (projectState id localStreamStacks base))
    (hm : base.stacks 18 = matrixFrames Q) (ht : base.stacks 19 = List.replicate t true)
    (hd : base.stacks 20 = List.replicate d true)
    (hp : base.stacks 22 = []) (htmp : base.stacks 23 = []) (hcopy : base.stacks 27 = []) :
    RejectionBody localCounterPorts 25 localStreamBody D
      (callbackBudget t D d + 68 * D + 24) base (rejectedRank (fun x => wordRejects Q x d)) := by
  constructor
  intro words a hw ha hc _
  have hlo (i : Fin 24) : a.stacks (localStreamStacks i) = base.stacks (localStreamStacks i) := by
    apply ha.1
    all_goals
      intro h
      have hv := congrArg Fin.val h
      simp [localStreamStacks, localCounterPorts] at hv
      omega
  obtain ⟨b, hb⟩ := ha.2
  obtain ⟨n, out, hn, hr, ho⟩ := local_stream_body Q d words hw a b
    (fun i => (hlo (wordStacks i)).trans (he i))
    ((hlo 18).trans hm) ((hlo 19).trans ht) ((hlo 20).trans hd)
    ((hlo 22).trans hp) ((hlo 23).trans htmp) hc hb
    ((ha.1 27 (by decide) (by decide) (by decide)).trans hcopy)
  exact ⟨n, out, hn, hr, by simpa [hb] using ho⟩

/-- The Walsh iterator likewise uses the actual graph arithmetic on every
valid character, and physically clears every invalid padded word. -/
theorem graph_rejection_body {D r : ℕ} (s : Fin D → Cayley.Cube r)
    (q : ℕ) (qbits Dbits : List Bool)
    (hqv : BinaryArithmetic.toNat qbits = q) (hDv : BinaryArithmetic.toNat Dbits = D)
    (base : ScanState) (he : GraphWorkEmpty (projectState id graphStreamStacks base))
    (hm : base.stacks 29 = matrixFrames s) (ht : base.stacks 30 = List.replicate D true)
    (hq : base.stacks 31 = qbits) (hD : base.stacks 32 = Dbits)
    (hp : base.stacks 34 = []) (htmp : base.stacks 35 = []) (hcopy : base.stacks 39 = []) :
    RejectionBody graphCounterPorts 37 graphStreamBody r
      (graphCallbackBudget D r qbits.length Dbits.length + 68 * r + 24) base
      (rejectedRank (fun x => graphWordRejects s x q)) := by
  constructor
  intro words a hw ha hc _
  have hlo (i : Fin 36) : a.stacks (graphStreamStacks i) = base.stacks (graphStreamStacks i) := by
    apply ha.1
    all_goals
      intro h
      have hv := congrArg Fin.val h
      simp [graphStreamStacks, graphCounterPorts] at hv
      omega
  obtain ⟨b, hb⟩ := ha.2
  obtain ⟨n, out, hn, hr, ho⟩ := graph_stream_body s q qbits Dbits hqv hDv words hw a b
    (fun i => (hlo (graphWordStacks i)).trans (he i))
    ((hlo 29).trans hm) ((hlo 30).trans ht) ((hlo 31).trans hq) ((hlo 32).trans hD)
    ((hlo 34).trans hp) ((hlo 35).trans htmp) hc hb
    ((ha.1 39 (by decide) (by decide) (by decide)).trans hcopy)
  exact ⟨n, out, hn, hr, by simpa [hb] using ho⟩

/-- The complete stream has a uniform prefix bound independent of its number
of iterations. Each body invocation uses only its polynomial local budget. -/
theorem rejection_visits_space {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (latch : Fin S) (hc : latch ≠ p.counter) (hs : latch ≠ p.scratch)
    (body : Cmd R S) (dimension budget : ℕ) (reject : ℕ → Bool)
    (base : State R S) (hbody : RejectionBody p latch body dimension budget base reject)
    (B : ℕ) (hB : 1 ≤ B) {a out : State R S} {ranks : List ℕ} {steps : ℕ}
    (hvis : ExecCNFTupleEnumeration.Visits p body (List.replicate dimension 2) ranks steps a out)
    (ha : RejectionFrame p latch base a) (hab : ∀ i, (a.stacks i).length ≤ B)
    (has : a.stacks p.scratch = []) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (compiled (ExecCNFTupleEnumeration.loopCmd p body) p.counter p.counter) prefixSteps
        (a.withPC (some (compiled (ExecCNFTupleEnumeration.loopCmd p body)
          p.counter p.counter).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤
        max (B + budget) (S * B + 7 * (6 * dimension + 1) + 4) := by
  let I : State R S → Prop := fun a => RejectionFrame p latch base a ∧
    (∀ i, (a.stacks i).length ≤ B) ∧ a.stacks p.scratch = []
  have hresult := Enumerators.visits_stack_bound p body (List.replicate dimension 2)
    I I B (B + budget) (fun _ h => h.2.1) (fun _ h => h.2.1)
    (by
      intro words start finish n hw hcounter he hI _
      obtain ⟨hn, hout⟩ := hbody.actual words start finish n hw hI.1 hcounter hI.2.2 he
      have hsfinish : finish.stacks p.scratch = [] := by
        rw [hout, Function.update_of_ne (Ne.symm hs)]
        exact hI.2.2
      refine ⟨⟨rejectionFrame_update p latch base start finish _ hI.1 hout, ?_, hsfinish⟩,
        hsfinish, ?_⟩
      · intro i
        by_cases hi : i = latch
        · subst i
          simpa [hout] using hB
        · rw [hout, Function.update_of_ne hi]
          exact hI.2.1 i
      · intro prefixSteps intermediate hle ht i
        have hg := OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le ht i
        change (intermediate.stacks i).length ≤ (start.stacks i).length + prefixSteps at hg
        have hi := hI.2.1 i
        omega)
    (by
      intro words state hw hcounter hI
      refine ⟨rejectionFrame_stable p latch hc hs base 0 state _
        (ExecCNFTupleEnumeration.advanceResult_outside p state words) hI.1, ?_,
        ExecCNFTupleEnumeration.advanceResult_scratch p state words⟩
      intro i
      by_cases hi : i = p.counter
      · subst i
        rw [ExecCNFTupleEnumeration.advanceResult_counter,
          ExecCNFTupleEnumeration.bumpWords_encoded_length, ← hcounter]
        exact hI.2.1 p.counter
      · by_cases hj : i = p.scratch
        · subst i
          simp
        · rw [← ExecCNFTupleEnumeration.advanceResult_outside p state words i hi hj]
          exact hI.2.1 i)
    hvis ⟨ha, hab, has⟩
  have hsize : 2 * (List.replicate dimension 2).sum +
      2 * (List.replicate dimension 2).length + 1 = 6 * dimension + 1 := by
    simp
    omega
  simpa only [hsize] using hresult

/-- Exhaustive rank rejection is equivalent to rejecting an actual field
word. This includes dimension zero and all invalid padded bit patterns. -/
theorem no_rejectedRank_iff {p d : ℕ} [Fact p.Prime]
    (hw : SubexpEnumerationPayload.scalarWidth p = 2)
    (reject : (Fin d → ZMod p) → Prop) [DecidablePred reject] :
    (List.range' 0 (4 ^ d)).any (rejectedRank reject) = false ↔ ∀ x, ¬ reject x := by
  classical
  constructor
  · intro h x hx
    have hp : 2 ^ (d * 2) = 4 ^ d := by
      rw [Nat.mul_comm d 2, pow_mul]
      norm_num
    have hlt := ExecCNFTupleOdometer.value_lt_power_length (CodeCandidates.fieldWords x).flatten
    rw [CodeCandidates.fieldWords_flatten_length, hw, hp] at hlt
    have hm : CounterPrograms.value (CodeCandidates.fieldWords x).flatten ∈
        List.range' 0 (4 ^ d) := by
      simpa only [List.mem_range'_1, Nat.zero_le, zero_add, true_and] using hlt
    have hn := List.any_eq_false.mp h _ hm
    rw [rejectedRank_field] at hn
    exact hn (decide_eq_true hx)
  · intro h
    apply List.any_eq_false.mpr
    intro rank _ htrue
    simp only [rejectedRank, decide_eq_true_eq] at htrue
    obtain ⟨x, _, hx⟩ := htrue
    exact h x hx

/-- Time and space hold on the same complete source trace. The uniform storage
bound contains no exponential iteration count. -/
theorem rejection_scan_runs_space {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (latch : Fin S) (hc : latch ≠ p.counter) (hs : latch ≠ p.scratch)
    (body : Cmd R S) (dimension budget : ℕ) (reject : ℕ → Bool)
    (a : State R S) (b : Bool)
    (hbody : RejectionBody p latch body dimension budget a reject)
    (hcounter : a.stacks p.counter =
      Encoding.encodeList id (List.replicate dimension [false, false]))
    (hscratch : a.stacks p.scratch = []) (hlatch : a.stacks latch = [b])
    (B : ℕ) (hB : 1 ≤ B) (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ n out, n ≤ 4 ^ dimension * (budget + 42 * dimension + 12) + 3 ∧
      Trace (ExecCNFTupleEnumeration.program p body) n
        (a.withPC (some (ExecCNFTupleEnumeration.program p body).entry)) (out.withPC none) ∧
      RejectionFrame p latch a out ∧ out.stacks p.scratch = [] ∧
      out.stacks latch = [b || (List.range' 0 (4 ^ dimension)).any reject] ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ n →
        Trace (ExecCNFTupleEnumeration.program p body) prefixSteps
          (a.withPC (some (ExecCNFTupleEnumeration.program p body).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          max (B + budget) (S * B + 7 * (6 * dimension + 1) + 4)) := by
  obtain ⟨n, out, hn, ht, hf, hsout, hlout⟩ := rejection_scan_runs p latch hc hs body
    dimension budget reject a b hbody hcounter hscratch hlatch
  have hi : RejectionFrame p latch a a := ⟨fun _ _ _ _ => rfl, b, hlatch⟩
  have stable := rejectionFrame_stable p latch hc hs a
  obtain ⟨m, other, he, hv, _, _, _, _⟩ :=
    ExecCNFTupleEnumeration.enumerate_correct p body (List.replicate dimension 2)
      (RejectionFrame p latch a) budget stable (hbody.bodySpec hc hs)
      (List.replicate dimension [false, false]) a (by simp) hi hcounter hscratch
      (ExecCNFTupleEnumeration.zero_tuple_value dimension 2)
  have hloop := rejection_visits_space p latch hc hs body dimension budget reject a hbody B hB hv
    (stable 0 a _ (fun _ _ _ => rfl) hi) ha hscratch
  have hspace := Enumerators.enumerate_stack_bound p body hv hloop
  have hnm := StreamResources.halted_trace_steps_eq ht
    (compiled_halt_trace he p.counter p.counter) (by rfl) (by rfl)
  refine ⟨n, out, hn, ht, hf, hsout, hlout, ?_⟩
  intro prefixSteps intermediate hle hprefix i
  apply hspace prefixSteps intermediate _ hprefix i
  rwa [← hnm]

private theorem stream_body_budget (c dimension : ℕ) :
    c + 68 * dimension + 24 + 42 * dimension + 12 = c + 110 * dimension + 36 := by
  omega

/-- An actual local-code scan decides the full distance property, with time
and all-prefix source space on the same trace, for any supplied matrix. -/
theorem local_stream_runs {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (d : ℕ) (a : ScanState)
    (he : WorkEmpty (projectState id localStreamStacks a))
    (hm : a.stacks 18 = matrixFrames Q) (ht : a.stacks 19 = List.replicate t true)
    (hd : a.stacks 20 = List.replicate d true)
    (hp : a.stacks 22 = []) (htmp : a.stacks 23 = []) (hcopy : a.stacks 27 = [])
    (hcounter : a.stacks 24 = Encoding.encodeList id (List.replicate D [false, false]))
    (hscratch : a.stacks 26 = []) (hlatch : a.stacks 25 = [false])
    (B : ℕ) (hB : 1 ≤ B) (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ n out, n ≤ localStreamBudget t D d ∧
      Trace (ExecCNFTupleEnumeration.program localCounterPorts localStreamBody) n
        (a.withPC (some (ExecCNFTupleEnumeration.program localCounterPorts localStreamBody).entry))
        (out.withPC none) ∧ RejectionFrame localCounterPorts 25 a out ∧ out.stacks 26 = [] ∧
      (out.stacks 25 = [false] ↔ SparseCode.HasDistance Q d) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ n →
        Trace (ExecCNFTupleEnumeration.program localCounterPorts localStreamBody) prefixSteps
          (a.withPC (some (ExecCNFTupleEnumeration.program localCounterPorts localStreamBody).entry))
          intermediate → ∀ i, (intermediate.stacks i).length ≤
            max (B + callbackBudget t D d + 68 * D + 24) (40 * B + 7 * (6 * D + 1) + 4)) := by
  obtain ⟨n, out, hn, htrace, hf, hs, hl, hspace⟩ := rejection_scan_runs_space
    localCounterPorts 25 (by decide) (by decide) localStreamBody D
    (callbackBudget t D d + 68 * D + 24) (rejectedRank (fun x => wordRejects Q x d)) a false
    (local_rejection_body Q d a he hm ht hd hp htmp hcopy) hcounter hscratch hlatch B hB ha
  refine ⟨n, out, ?_, htrace, hf, hs, ?_, ?_⟩
  · simpa only [localStreamBudget, stream_body_budget] using hn
  · rw [hl]
    simp only [Bool.false_or, List.cons.injEq, and_true]
    rw [no_rejectedRank_iff (by norm_num [SubexpEnumerationPayload.scalarWidth])]
    exact no_local_rejection_iff Q
  · simpa only [Nat.add_assoc] using hspace

/-- The actual Walsh scan similarly decides Good for every supplied graph,
including failed candidates and the zero-dimensional character space. -/
theorem graph_stream_runs {D r : ℕ} (s : Fin D → Cayley.Cube r)
    (q : ℕ) (qbits Dbits : List Bool)
    (hqv : BinaryArithmetic.toNat qbits = q) (hDv : BinaryArithmetic.toNat Dbits = D)
    (a : ScanState) (he : GraphWorkEmpty (projectState id graphStreamStacks a))
    (hm : a.stacks 29 = matrixFrames s) (ht : a.stacks 30 = List.replicate D true)
    (hq : a.stacks 31 = qbits) (hD : a.stacks 32 = Dbits)
    (hp : a.stacks 34 = []) (htmp : a.stacks 35 = []) (hcopy : a.stacks 39 = [])
    (hcounter : a.stacks 36 = Encoding.encodeList id (List.replicate r [false, false]))
    (hscratch : a.stacks 38 = []) (hlatch : a.stacks 37 = [false])
    (B : ℕ) (hB : 1 ≤ B) (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ n out, n ≤ graphStreamBudget D r qbits.length Dbits.length ∧
      Trace (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody) n
        (a.withPC (some (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody).entry))
        (out.withPC none) ∧ RejectionFrame graphCounterPorts 37 a out ∧ out.stacks 38 = [] ∧
      (out.stacks 37 = [false] ↔ WalshExistence.Good q s) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ n →
        Trace (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody) prefixSteps
          (a.withPC (some (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody).entry))
          intermediate → ∀ i, (intermediate.stacks i).length ≤
            max (B + graphCallbackBudget D r qbits.length Dbits.length + 68 * r + 24)
              (40 * B + 7 * (6 * r + 1) + 4)) := by
  obtain ⟨n, out, hn, htrace, hf, hs, hl, hspace⟩ := rejection_scan_runs_space
    graphCounterPorts 37 (by decide) (by decide) graphStreamBody r
    (graphCallbackBudget D r qbits.length Dbits.length + 68 * r + 24)
    (rejectedRank (fun x => graphWordRejects s x q)) a false
    (graph_rejection_body s q qbits Dbits hqv hDv a he hm ht hq hD hp htmp hcopy)
    hcounter hscratch hlatch B hB ha
  refine ⟨n, out, ?_, htrace, hf, hs, ?_, ?_⟩
  · simpa only [graphStreamBudget, stream_body_budget] using hn
  · rw [hl]
    simp only [Bool.false_or, List.cons.injEq, and_true]
    rw [no_rejectedRank_iff (by norm_num [SubexpEnumerationPayload.scalarWidth])]
    exact no_graph_rejection_iff s q
  · simpa only [Nat.add_assoc] using hspace

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks



namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

/-- The runtime dimension is preserved; every other port here is temporary. -/
def localScanPorts : CodeCandidateProgram.ScanPorts 40 where
  stack := ⟨![21, 27, 24, 23, 25], by decide⟩

def graphScanPorts : CodeCandidateProgram.ScanPorts 40 where
  stack := ⟨![33, 39, 36, 35, 37], by decide⟩

def localChecker : Cmd 16 40 := CodeCandidateProgram.scanWrapper localScanPorts
  (ExecCNFTupleEnumeration.program localCounterPorts localStreamBody)

def graphChecker : Cmd 16 40 := CodeCandidateProgram.scanWrapper graphScanPorts
  (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody)

/-- The core workspace is polynomial in the initial retained data and one
candidate's arithmetic budget, independently of how many words are checked. -/
def coreSpace (A dimension callbackCost : ℕ) : ℕ :=
  max (A + 6 * dimension + 1 + callbackCost + 68 * dimension + 24)
    (40 * (A + 6 * dimension + 1) + 7 * (6 * dimension + 1) + 4)

private theorem zero_tuple_encoded_length (d : ℕ) :
    (Encoding.encodeList id (List.replicate d [false, false])).length = 6 * d + 1 := by
  rw [Enumerators.encoded_shape_length (by simp :
    (List.replicate d [false, false]).map List.length = List.replicate d 2)]
  simp
  omega

private theorem scan_prepared_bound {S A : ℕ} (p : CodeCandidateProgram.ScanPorts S)
    (a prepared : State 16 S) (ha : ∀ i, (a.stacks i).length ≤ A)
    (hp : prepared.stacks = CodeCandidateProgram.scanPreparedStacks p a) :
    ∀ i, (prepared.stacks i).length ≤ A + 6 * (a.stacks (p.stack 0)).length + 1 := by
  intro i
  rw [hp]
  unfold CodeCandidateProgram.scanPreparedStacks
  by_cases hi : i = p.stack 4
  · subst i
    simp
  · rw [Function.update_of_ne hi]
    by_cases hj : i = p.stack 2
    · subst i
      rw [Function.update_self, zero_tuple_encoded_length]
      omega
    · rw [Function.update_of_ne hj]
      have hb := ha i
      omega

private theorem rejection_bool (bit : Bool) (P : Prop) [Decidable P]
    (h : bit = false ↔ P) : bit = !(decide P) := by
  cases bit <;> simp_all

/-- Complete actual local-matrix checker: it initializes its word counter,
checks every word, computes the Boolean acceptance bit, then clears temporary
state. Time and the uniform source-prefix space bound describe the same run. -/
theorem local_checker_runs {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (d : ℕ) (a : ScanState) (A : ℕ) (ha : ∀ i, (a.stacks i).length ≤ A)
    (he : WorkEmpty (projectState id localStreamStacks a))
    (hm : a.stacks 18 = matrixFrames Q) (ht : a.stacks 19 = List.replicate t true)
    (hd : a.stacks 20 = List.replicate d true) (hD : a.stacks 21 = List.replicate D true)
    (hp : a.stacks 22 = []) (htmp : a.stacks 23 = []) (hcounter : a.stacks 24 = [])
    (hlatch : a.stacks 25 = []) (hscratch : a.stacks 26 = []) (hcopy : a.stacks 27 = []) :
    ∃ steps out, Eval localChecker steps a out ∧
      steps ≤ localStreamBudget t D d + 15 * D + 2 * coreSpace A D (callbackBudget t D d) + 18 ∧
      (out.regs 15 = true ↔ SparseCode.HasDistance Q d) ∧ out.stacks = a.stacks ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace (compiled localChecker 21 25) prefixSteps
          (a.withPC (some (compiled localChecker 21 25).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          40 * A + 15 * D + 43 * coreSpace A D (callbackBudget t D d) + 18) := by
  classical
  have hcore : ∀ prepared : ScanState,
      prepared.stacks = CodeCandidateProgram.scanPreparedStacks localScanPorts a →
      ∃ (n : ℕ) (middle : ScanState), n ≤ localStreamBudget t D d ∧
        Trace (ExecCNFTupleEnumeration.program localCounterPorts localStreamBody) n
          (prepared.withPC (some (ExecCNFTupleEnumeration.program localCounterPorts localStreamBody).entry))
          (middle.withPC none) ∧
        middle.stacks 25 = [!(decide (SparseCode.HasDistance Q d))] ∧
        (∀ i, i ≠ 24 → i ≠ 25 → middle.stacks i = prepared.stacks i) ∧
        ∀ prefixSteps intermediate, prefixSteps ≤ n →
          Trace (ExecCNFTupleEnumeration.program localCounterPorts localStreamBody) prefixSteps
            (prepared.withPC (some (ExecCNFTupleEnumeration.program localCounterPorts localStreamBody).entry))
            intermediate → ∀ i, (intermediate.stacks i).length ≤ coreSpace A D (callbackBudget t D d) := by
    intro prepared hprepared
    have hf (i : Fin 40) (hi : i ≠ 24) (hj : i ≠ 25) : prepared.stacks i = a.stacks i := by
      rw [hprepared]
      simp [CodeCandidateProgram.scanPreparedStacks, localScanPorts, hi, hj]
    have hb : ∀ i, (prepared.stacks i).length ≤ A + 6 * D + 1 := by
      simpa [localScanPorts, hD] using scan_prepared_bound localScanPorts a prepared ha hprepared
    have hcounter' : prepared.stacks 24 = Encoding.encodeList id (List.replicate D [false, false]) := by
      rw [hprepared]
      simp [CodeCandidateProgram.scanPreparedStacks, localScanPorts, hD]
    have hlatch' : prepared.stacks 25 = [false] := by
      rw [hprepared]
      simp [CodeCandidateProgram.scanPreparedStacks, localScanPorts]
    have he' : WorkEmpty (projectState id localStreamStacks prepared) := by
      intro i
      apply (hf _ ?_ ?_).trans (he i)
      all_goals
        intro h
        have hv := congrArg Fin.val h
        change i.val = _ at hv
        have hi := i.isLt
        omega
    obtain ⟨n, middle, hn, htrace, hframe, hscratch', hdecide, hspace⟩ :=
      local_stream_runs Q d prepared he' ((hf 18 (by decide) (by decide)).trans hm)
        ((hf 19 (by decide) (by decide)).trans ht) ((hf 20 (by decide) (by decide)).trans hd)
        ((hf 22 (by decide) (by decide)).trans hp) ((hf 23 (by decide) (by decide)).trans htmp)
        ((hf 27 (by decide) (by decide)).trans hcopy) hcounter'
        ((hf 26 (by decide) (by decide)).trans hscratch) hlatch'
        (A + 6 * D + 1) (by omega) hb
    obtain ⟨bit, hbit⟩ := hframe.latch_word
    have hbitvalue : bit = !(decide (SparseCode.HasDistance Q d)) :=
      rejection_bool bit _ (by simpa [hbit] using hdecide)
    refine ⟨n, middle, hn, htrace, hbit.trans (congrArg List.singleton hbitvalue), ?_, hspace⟩
    intro i hi hj
    by_cases hs : i = 26
    · subst i
      exact hscratch'.trans ((hf 26 (by decide) (by decide)).trans hscratch).symm
    · exact hframe.frame i hi hs hj
  obtain ⟨steps, out, hrun, htime, hanswer, hout, hspace⟩ :=
    CodeCandidateProgram.scanWrapper_resources localScanPorts
      (ExecCNFTupleEnumeration.program localCounterPorts localStreamBody)
      a (!(decide (SparseCode.HasDistance Q d))) hcopy hcounter htmp hlatch ha hcore
  refine ⟨steps, out, hrun, ?_, ?_, hout, ?_⟩
  · simpa [localScanPorts, hD] using htime
  · simp only [hanswer, Bool.not_not, decide_eq_true_eq]
  · have hsum (A d b : ℕ) : 40 * A + 15 * d + 40 * b + 3 * b + 18 =
        40 * A + 15 * d + 43 * b + 18 := by omega
    simpa [localChecker, localScanPorts, hD, hsum] using hspace

/-- Complete actual graph-matrix checker: it initializes its word counter,
checks every word, computes the Boolean acceptance bit, then clears temporary
state. Time and the uniform source-prefix space bound describe the same run. -/
theorem graph_checker_runs {D r : ℕ} (s : Fin D → Cayley.Cube r)
    (q : ℕ) (qbits Dbits : List Bool)
    (hqv : BinaryArithmetic.toNat qbits = q) (hDv : BinaryArithmetic.toNat Dbits = D) (a : ScanState) (A : ℕ) (ha : ∀ i, (a.stacks i).length ≤ A)
    (he : GraphWorkEmpty (projectState id graphStreamStacks a))
    (hm : a.stacks 29 = matrixFrames s) (ht : a.stacks 30 = List.replicate D true)
    (hq : a.stacks 31 = qbits) (hDbits : a.stacks 32 = Dbits) (hr : a.stacks 33 = List.replicate r true)
    (hp : a.stacks 34 = []) (htmp : a.stacks 35 = []) (hcounter : a.stacks 36 = [])
    (hlatch : a.stacks 37 = []) (hscratch : a.stacks 38 = []) (hcopy : a.stacks 39 = []) :
    ∃ steps out, Eval graphChecker steps a out ∧
      steps ≤ graphStreamBudget D r qbits.length Dbits.length + 15 * r + 2 * coreSpace A r (graphCallbackBudget D r qbits.length Dbits.length) + 18 ∧
      (out.regs 15 = true ↔ WalshExistence.Good q s) ∧ out.stacks = a.stacks ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace (compiled graphChecker 33 37) prefixSteps
          (a.withPC (some (compiled graphChecker 33 37).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          40 * A + 15 * r + 43 * coreSpace A r (graphCallbackBudget D r qbits.length Dbits.length) + 18) := by
  classical
  have hcore : ∀ prepared : ScanState,
      prepared.stacks = CodeCandidateProgram.scanPreparedStacks graphScanPorts a →
      ∃ (n : ℕ) (middle : ScanState), n ≤ graphStreamBudget D r qbits.length Dbits.length ∧
        Trace (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody) n
          (prepared.withPC (some (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody).entry))
          (middle.withPC none) ∧
        middle.stacks 37 = [!(decide (WalshExistence.Good q s))] ∧
        (∀ i, i ≠ 36 → i ≠ 37 → middle.stacks i = prepared.stacks i) ∧
        ∀ prefixSteps intermediate, prefixSteps ≤ n →
          Trace (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody) prefixSteps
            (prepared.withPC (some (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody).entry))
            intermediate → ∀ i, (intermediate.stacks i).length ≤ coreSpace A r (graphCallbackBudget D r qbits.length Dbits.length) := by
    intro prepared hprepared
    have hf (i : Fin 40) (hi : i ≠ 36) (hj : i ≠ 37) : prepared.stacks i = a.stacks i := by
      rw [hprepared]
      simp [CodeCandidateProgram.scanPreparedStacks, graphScanPorts, hi, hj]
    have hb : ∀ i, (prepared.stacks i).length ≤ A + 6 * r + 1 := by
      simpa [graphScanPorts, hr] using scan_prepared_bound graphScanPorts a prepared ha hprepared
    have hcounter' : prepared.stacks 36 = Encoding.encodeList id (List.replicate r [false, false]) := by
      rw [hprepared]
      simp [CodeCandidateProgram.scanPreparedStacks, graphScanPorts, hr]
    have hlatch' : prepared.stacks 37 = [false] := by
      rw [hprepared]
      simp [CodeCandidateProgram.scanPreparedStacks, graphScanPorts]
    have he' : GraphWorkEmpty (projectState id graphStreamStacks prepared) := by
      intro i
      apply (hf _ ?_ ?_).trans (he i)
      all_goals
        intro h
        have hv := congrArg Fin.val h
        change i.val = _ at hv
        have hi := i.isLt
        omega
    obtain ⟨n, middle, hn, htrace, hframe, hscratch', hdecide, hspace⟩ :=
      graph_stream_runs s q qbits Dbits hqv hDv prepared he' ((hf 29 (by decide) (by decide)).trans hm)
        ((hf 30 (by decide) (by decide)).trans ht) ((hf 31 (by decide) (by decide)).trans hq)
        ((hf 32 (by decide) (by decide)).trans hDbits)
        ((hf 34 (by decide) (by decide)).trans hp) ((hf 35 (by decide) (by decide)).trans htmp)
        ((hf 39 (by decide) (by decide)).trans hcopy) hcounter'
        ((hf 38 (by decide) (by decide)).trans hscratch) hlatch'
        (A + 6 * r + 1) (by omega) hb
    obtain ⟨bit, hbit⟩ := hframe.latch_word
    have hbitvalue : bit = !(decide (WalshExistence.Good q s)) :=
      rejection_bool bit _ (by simpa [hbit] using hdecide)
    refine ⟨n, middle, hn, htrace, hbit.trans (congrArg List.singleton hbitvalue), ?_, hspace⟩
    intro i hi hj
    by_cases hs : i = 38
    · subst i
      exact hscratch'.trans ((hf 38 (by decide) (by decide)).trans hscratch).symm
    · exact hframe.frame i hi hs hj
  obtain ⟨steps, out, hrun, htime, hanswer, hout, hspace⟩ :=
    CodeCandidateProgram.scanWrapper_resources graphScanPorts
      (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody)
      a (!(decide (WalshExistence.Good q s))) hcopy hcounter htmp hlatch ha hcore
  refine ⟨steps, out, hrun, ?_, ?_, hout, ?_⟩
  · simpa [graphScanPorts, hr] using htime
  · simp only [hanswer, Bool.not_not, decide_eq_true_eq]
  · have hsum (A q b : ℕ) : 40 * A + 15 * q + 40 * b + 3 * b + 18 =
        40 * A + 15 * q + 43 * b + 18 := by omega
    simpa [graphChecker, graphScanPorts, hr, hsum] using hspace

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

/-- The outer search retains only its current tuple, first witness, and a
constant number of linear-size conversion buffers above the checker's ports. -/
abbrev MatrixState := State 16 48

def checkerPorts : Fin 40 → Fin 48 := Fin.castAdd 8

def liftChecker (checker : Cmd 16 40) (input output : Fin 40) : Cmd 16 48 :=
  .call (ProgramLinking.liftProgram (compiled checker input output) id checkerPorts)

/-- A complete checker call keeps its local every-prefix space proof after
embedding; the eight persistent outer-search stacks are counted separately. -/
theorem lift_checker_resources (checker : Cmd 16 40) (input output : Fin 40)
    (a : MatrixState) (small : ScanState) {n A B : ℕ}
    (hrun : Eval checker n (projectState id checkerPorts a) small)
    (hrestore : small.stacks = (projectState id checkerPorts a).stacks)
    (ha : ∀ i, (a.stacks i).length ≤ A)
    (hspace : ∀ k c, k ≤ n → Trace (compiled checker input output) k
      ((projectState id checkerPorts a).withPC (some (compiled checker input output).entry)) c →
      ∀ i, (c.stacks i).length ≤ B) :
    ∃ out, Eval (liftChecker checker input output) (n + 1) a out ∧
      out.stacks = a.stacks ∧ out.regs = small.regs ∧
      (∀ k c, k ≤ n + 1 → Trace (compiled (liftChecker checker input output) 40 42) k
        (a.withPC (some (compiled (liftChecker checker input output) 40 42).entry)) c →
        ∀ i, (c.stacks i).length ≤ max B A) := by
  let out := embedState id checkerPorts a small
  have ht := compiled_halt_trace hrun input output
  have hs := StructuredSpace.compiled_halt_stack_bound hrun input output hspace
  have hc := eval_call_from_state (compiled checker input output) id checkerPorts a
    Function.injective_id (Fin.castAdd_injective _ _) ht
  have hinitial : ProgramLinking.embedCfg id checkerPorts id none
      (a.withPC (none : Option (Fin (size checker + 1))))
      ((projectState id checkerPorts a).withPC (some (compiled checker input output).entry)) =
      a.withPC (some (compiled checker input output).entry) := by
    change (embedState id checkerPorts a (projectState id checkerPorts a)).withPC _ = _
    rw [embedState_project id checkerPorts a Function.injective_id (Fin.castAdd_injective _ _)]
    rfl
  have hlift := ProgramLinking.liftProgram_trace (compiled checker input output) id checkerPorts
    (a.withPC none) Function.injective_id (Fin.castAdd_injective _ _) ht
  rw [hinitial] at hlift
  have hlift' : Trace (ProgramLinking.liftProgram (compiled checker input output) id checkerPorts)
      (n + 1) (a.withPC (some (compiled checker input output).entry)) (out.withPC none) := by
    simpa [out, embedState, ProgramLinking.embedCfg, ProgramLinking.relocatePc,
      StructuredProgram.State.withPC] using hlift
  have hliftspace := StructuredSpace.liftProgram_stack_bound
    (compiled checker input output) id checkerPorts (a.withPC none)
    Function.injective_id (Fin.castAdd_injective _ _) ht hs ha
  rw [hinitial] at hliftspace
  refine ⟨out, hc, ?_, ?_, ?_⟩
  · funext i
    by_cases hi : ∃ j, checkerPorts j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (embedState_stack id checkerPorts a small (Fin.castAdd_injective _ _) j).trans
        (congrFun hrestore j)
    · exact embedState_stack_frame id checkerPorts a small i hi
  · funext i
    exact embedState_register id checkerPorts a small Function.injective_id i
  · exact StructuredSpace.call_stack_bound
      (ProgramLinking.liftProgram (compiled checker input output) id checkerPorts)
      (compiled (liftChecker checker input output) 40 42)
      (siteAddress (liftChecker checker input output)) (exitAddress (liftChecker checker input output))
      (compiled_site (liftChecker checker input output) 40 42) hlift' hliftspace

/-- The branch accepts only properly encoded matrices; the actual checker
then decides its algebraic property by its inner complete word scan. -/
def matrixCandidate (ternary : Bool) (matrix : Fin 48)
    (checker : Cmd 16 40) (input output : Fin 40) : Cmd 16 48 :=
  .seq (copyConvertCommand ternary 40 43 44 45) <|
  .ite 4
    (.seq (SubexpSetupStorage.clearCmd 44) (.base (.atom (.set 15 false))))
    (.seq (installMatrix 44 matrix) (liftChecker checker input output))

def localMatrixCandidate : Cmd 16 48 := matrixCandidate true 18 localChecker 21 25

def graphMatrixCandidate : Cmd 16 48 := matrixCandidate false 29 graphChecker 33 37

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

/-- Invalid matrix digits are rejected by actual finite control and all of
conversion's retained buffers are cleared. -/
theorem matrix_candidate_invalid (ternary : Bool) (matrix : Fin 48)
    (checker : Cmd 16 40) (input output : Fin 40)
    (xs : List (Bool × Bool)) (a : MatrixState) (A : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ A)
    (hcurrent : a.stacks 40 = CodeCandidates.tupleBits xs)
    (hinput : a.stacks 43 = []) (hpayload : a.stacks 44 = []) (hscratch : a.stacks 45 = [])
    (hbad : xs.any (CodeCandidates.invalidDigit ternary) = true) :
    ∃ out, Eval (matrixCandidate ternary matrix checker input output)
        (68 * xs.length + 21) a out ∧
      out.regs 15 = false ∧ out.stacks = a.stacks ∧
      (∀ k c, k ≤ 68 * xs.length + 21 →
        Trace (compiled (matrixCandidate ternary matrix checker input output) 40 42) k
          (a.withPC (some (compiled (matrixCandidate ternary matrix checker input output) 40 42).entry)) c →
        ∀ i, (c.stacks i).length ≤ A + 68 * xs.length + 21) := by
  obtain ⟨b, hc, hf, _, hw, hframe⟩ := copy_convert_eval ternary 40 43 44 45
    (by decide) (by decide) (by decide) (by decide) xs a hcurrent hinput hpayload hscratch
  let cleared := SubexpSetupStorage.clearState 44 b
  let out := (StructuredProgram.Atom.set (s := 48) 15 false).eval cleared
  have hclear := SubexpSetupStorage.clear_eval 44 b
  rw [hw, List.length_reverse, CodeCandidates.scalarFrames_length] at hclear
  have hr : Eval (matrixCandidate ternary matrix checker input output)
      (68 * xs.length + 21) a out := by
    have h := hc.seq (Eval.ite_true (no := .seq (installMatrix 44 matrix)
      (liftChecker checker input output)) (hf.trans hbad)
      (hclear.seq (Eval.base (.atom (.set 15 false) cleared))))
    convert h using 1
    · rfl
    · omega
  refine ⟨out, hr, by simp [out, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    execInstr, StructuredProgram.State.ofCfg], ?_, ?_⟩
  · obtain ⟨out', hr', hout'⟩ := invalid_conversion_eval ternary 40 43 44 45
      (.seq (installMatrix 44 matrix) (liftChecker checker input output))
      (by decide) (by decide) (by decide) (by decide) xs a hcurrent hinput hpayload hscratch hbad
    have hclearstacks : cleared.stacks = a.stacks := by
      have h := hc.seq (Eval.ite_true (no := .seq (installMatrix 44 matrix)
        (liftChecker checker input output)) (hf.trans hbad) hclear)
      have heq := Eval.final_unique 40 h hr'
      exact congrArg StructuredProgram.State.stacks heq |>.trans hout'
    simpa [out, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, execInstr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC] using hclearstacks
  · intro k c hk ht i
    have hg := OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le ht i
    change (c.stacks i).length ≤ (a.stacks i).length + k at hg
    have hi := ha i
    omega

/-- This composition lemma charges conversion and replacement locally, while
using the separately proved complete checker's space bound for its long scan.
The next two theorems instantiate this interface with the actual checkers. -/
theorem matrix_candidate_valid (ternary : Bool) (matrix : Fin 48)
    (checker : Cmd 16 40) (input output : Fin 40)
    (hm43 : matrix ≠ 43) (hm44 : matrix ≠ 44)
    (xs : List (Bool × Bool)) (word : List Bool) (hword : CodeCandidates.scalarFrames xs = word)
    (a : MatrixState) (A T B : ℕ) (P : Prop)
    (ha : ∀ i, (a.stacks i).length ≤ A)
    (hcurrent : a.stacks 40 = CodeCandidates.tupleBits xs)
    (hinput : a.stacks 43 = []) (hpayload : a.stacks 44 = []) (hscratch : a.stacks 45 = [])
    (hvalid : xs.any (CodeCandidates.invalidDigit ternary) = false)
    (hchecker : ∀ prepared : MatrixState, prepared.stacks = Function.update a.stacks matrix word →
      ∃ n out, n ≤ T ∧ Eval (liftChecker checker input output) n prepared out ∧
        (out.regs 15 = true ↔ P) ∧ out.stacks = prepared.stacks ∧
        ∀ k c, k ≤ n → Trace (compiled (liftChecker checker input output) 40 42) k
          (prepared.withPC (some (compiled (liftChecker checker input output) 40 42).entry)) c →
          ∀ i, (c.stacks i).length ≤ B) :
    ∃ n out, n ≤ T + 2 * A + 73 * xs.length + 23 ∧
      Eval (matrixCandidate ternary matrix checker input output) n a out ∧
      (out.regs 15 = true ↔ P) ∧ out.stacks = Function.update a.stacks matrix word ∧
      (∀ k c, k ≤ n → Trace (compiled (matrixCandidate ternary matrix checker input output) 40 42) k
        (a.withPC (some (compiled (matrixCandidate ternary matrix checker input output) 40 42).entry)) c →
        ∀ i, (c.stacks i).length ≤ max (3 * A + 73 * xs.length + 23) B) := by
  obtain ⟨b, hcopy, hflag, hb43, hb44, hbframe⟩ := copy_convert_eval ternary 40 43 44 45
    (by decide) (by decide) (by decide) (by decide) xs a hcurrent hinput hpayload hscratch
  have hbm : b.stacks matrix = a.stacks matrix := hbframe matrix hm43 hm44
  have hwlen : word.length = 5 * xs.length := by
    rw [← hword, CodeCandidates.scalarFrames_length]
  obtain ⟨prepared, hinstall, hp44, hpm, hpframe⟩ := installMatrix_eval 44 matrix (Ne.symm hm44)
    word b (by rw [hb44, hword])
  have hprepared : prepared.stacks = Function.update a.stacks matrix word := by
    funext i
    by_cases hi : i = matrix
    · subst i
      simpa using hpm
    · rw [Function.update_of_ne hi]
      by_cases h44 : i = 44
      · subst i
        exact hp44.trans hpayload.symm
      · rw [hpframe i h44 hi]
        by_cases h43 : i = 43
        · subst i
          exact hb43.trans hinput.symm
        · exact hbframe i h43 h44
  obtain ⟨n, out, hn, hcheck, haccept, hrestore, hcheckspace⟩ := hchecker prepared hprepared
  let bound := max (3 * A + 73 * xs.length + 23) B
  have hcopyspace : ∀ k c, k ≤ 58 * xs.length + 16 →
      Trace (compiled (copyConvertCommand ternary 40 43 44 45) 40 42) k
        (a.withPC (some (compiled (copyConvertCommand ternary 40 43 44 45) 40 42).entry)) c →
        ∀ i, (c.stacks i).length ≤ bound := by
    intro k c hk ht i
    have hg := OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le ht i
    change (c.stacks i).length ≤ (a.stacks i).length + k at hg
    have hi := ha i
    exact (by omega : (c.stacks i).length ≤ 3 * A + 73 * xs.length + 23).trans (Nat.le_max_left _ _)
  have hinstallspace : ∀ k c, k ≤ 2 * (b.stacks matrix).length + 3 * word.length + 6 →
      Trace (compiled (installMatrix 44 matrix) 40 42) k
        (b.withPC (some (compiled (installMatrix 44 matrix) 40 42).entry)) c →
        ∀ i, (c.stacks i).length ≤ bound := by
    intro k c hk ht i
    have hg := OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le ht i
    have hb := OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le (compiled_trace hcopy 40 42) i
    change (c.stacks i).length ≤ (b.stacks i).length + k at hg
    change (b.stacks i).length ≤ (a.stacks i).length + (58 * xs.length + 16) at hb
    have hi := ha i
    have hm := ha matrix
    rw [hbm, hwlen] at hk
    exact (by omega : (c.stacks i).length ≤ 3 * A + 73 * xs.length + 23).trans (Nat.le_max_left _ _)
  have hcheckspace' : ∀ k c, k ≤ n → Trace (compiled (liftChecker checker input output) 40 42) k
      (prepared.withPC (some (compiled (liftChecker checker input output) 40 42).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
    intro k c hk ht i
    exact (hcheckspace k c hk ht i).trans (Nat.le_max_right _ _)
  have hsequence := StructuredSpace.sequence_stack_bound hinstall hcheck 40 42 hinstallspace hcheckspace'
    (compiled (.seq (installMatrix 44 matrix) (liftChecker checker input output)) 40 42)
    (siteAddress (.seq (installMatrix 44 matrix) (liftChecker checker input output)))
    (exitAddress (.seq (installMatrix 44 matrix) (liftChecker checker input output)))
    (compiled_site _ 40 42)
  let rejected : Cmd 16 48 := .seq (SubexpSetupStorage.clearCmd 44) (.base (.atom (.set 15 false)))
  let tail : Cmd 16 48 := .ite 4 rejected (.seq (installMatrix 44 matrix) (liftChecker checker input output))
  have htail : Eval tail ((2 * (b.stacks matrix).length + 3 * word.length + 6 + n) + 1) b out :=
    .ite_false (hflag.trans hvalid) (hinstall.seq hcheck)
  have htailspace := StructuredSpace.conditional_false_stack_bound (hflag.trans hvalid)
    (hinstall.seq hcheck) 40 42 hsequence (compiled tail 40 42) (siteAddress tail)
    (exitAddress tail) (compiled_site tail 40 42)
  refine ⟨(58 * xs.length + 16) + ((2 * (b.stacks matrix).length + 3 * word.length + 6 + n) + 1), out,
    ?_, hcopy.seq htail, haccept, hrestore.trans hprepared, ?_⟩
  · have hm := ha matrix
    rw [hbm, hwlen]
    omega
  · exact StructuredSpace.sequence_stack_bound hcopy htail 40 42 hcopyspace htailspace
      (compiled (matrixCandidate ternary matrix checker input output) 40 42)
      (siteAddress (matrixCandidate ternary matrix checker input output))
      (exitAddress (matrixCandidate ternary matrix checker input output))
      (compiled_site (matrixCandidate ternary matrix checker input output) 40 42)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

def matrixCheckTime (A matrixDimension wordDimension callbackCost streamCost : ℕ) : ℕ :=
  streamCost + 15 * wordDimension + 2 * coreSpace (A + 5 * matrixDimension) wordDimension callbackCost + 19

def matrixCheckSpace (A matrixDimension wordDimension callbackCost : ℕ) : ℕ :=
  max (40 * (A + 5 * matrixDimension) + 15 * wordDimension +
    43 * coreSpace (A + 5 * matrixDimension) wordDimension callbackCost + 18)
    (A + 5 * matrixDimension)

private theorem updated_matrix_bound (a prepared : MatrixState) (A : ℕ) (matrix : Fin 48)
    (word : List Bool) (ha : ∀ i, (a.stacks i).length ≤ A)
    (hp : prepared.stacks = Function.update a.stacks matrix word) :
    ∀ i, (prepared.stacks i).length ≤ A + word.length := by
  intro i
  rw [hp]
  by_cases hi : i = matrix
  · subst i
    simp
  · rw [Function.update_of_ne hi]
    exact (ha i).trans (Nat.le_add_right _ _)

theorem local_matrix_candidate_valid {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (d : ℕ) (xs : List (Bool × Bool))
    (hfields : xs.map CodeCandidates.digitBits = CodeCandidates.matrixWords Q)
    (hvalid : xs.any (CodeCandidates.invalidDigit true) = false)
    (a : MatrixState) (A : ℕ) (ha : ∀ i, (a.stacks i).length ≤ A)
    (he : ∀ i : Fin 18, a.stacks (Fin.castAdd 30 i) = [])
    (ht : a.stacks 19 = List.replicate t true) (hd : a.stacks 20 = List.replicate d true)
    (hD : a.stacks 21 = List.replicate D true)
    (hp : a.stacks 22 = []) (htmp : a.stacks 23 = []) (hcounter : a.stacks 24 = [])
    (hlatch : a.stacks 25 = []) (hscratch : a.stacks 26 = []) (hcopy : a.stacks 27 = [])
    (hcurrent : a.stacks 40 = CodeCandidates.tupleBits xs)
    (hinput : a.stacks 43 = []) (hpayload : a.stacks 44 = []) (houtertmp : a.stacks 45 = []) :
    ∃ n out, n ≤ matrixCheckTime A (t * D) D (callbackBudget t D d) (localStreamBudget t D d) +
        2 * A + 73 * (t * D) + 23 ∧
      Eval localMatrixCandidate n a out ∧
      (out.regs 15 = true ↔ SparseCode.HasDistance Q d) ∧
      out.stacks = Function.update a.stacks 18 (matrixFrames Q) ∧
      (∀ k c, k ≤ n → Trace (compiled localMatrixCandidate 40 42) k
        (a.withPC (some (compiled localMatrixCandidate 40 42).entry)) c →
        ∀ i, (c.stacks i).length ≤ max (3 * A + 73 * (t * D) + 23)
          (matrixCheckSpace A (t * D) D (callbackBudget t D d))) := by
  have hlen : xs.length = t * D := by simpa [CodeCandidates.matrixWords] using congrArg List.length hfields
  have hword := pair_matrix_frames_eq xs Q hfields
  have hwordlen : (matrixFrames Q).length = 5 * (t * D) := by
    rw [← hword, CodeCandidates.scalarFrames_length, hlen]
  have result := matrix_candidate_valid true 18 localChecker 21 25
      (by decide) (by decide) xs (matrixFrames Q) hword a A
      (matrixCheckTime A (t * D) D (callbackBudget t D d) (localStreamBudget t D d))
      (matrixCheckSpace A (t * D) D (callbackBudget t D d)) (SparseCode.HasDistance Q d)
      ha hcurrent hinput hpayload houtertmp hvalid
  rw [hlen] at result
  apply result
  intro prepared hprepared
  have hf (i : Fin 48) (hi : i ≠ 18) : prepared.stacks i = a.stacks i := by
    rw [hprepared, Function.update_of_ne hi]
  have hb : ∀ i, (prepared.stacks i).length ≤ A + 5 * (t * D) := by
    simpa [hwordlen] using updated_matrix_bound a prepared A 18 (matrixFrames Q) ha hprepared
  have he' : WorkEmpty (projectState id localStreamStacks (projectState id checkerPorts prepared)) := by
    intro i
    apply (hf (Fin.castAdd 30 i) ?_).trans (he i)
    intro h
    have hv := congrArg Fin.val h
    change i.val = 18 at hv
    omega
  have hm : (projectState id checkerPorts prepared).stacks 18 = matrixFrames Q := by
    change prepared.stacks 18 = _
    rw [hprepared, Function.update_self]
  obtain ⟨n, small, hrun, hn, haccept, hrestore, hspace⟩ := local_checker_runs Q d
    (projectState id checkerPorts prepared) (A + 5 * (t * D)) (fun i => hb (checkerPorts i)) he' hm
    ((hf 19 (by decide)).trans ht) ((hf 20 (by decide)).trans hd) ((hf 21 (by decide)).trans hD)
    ((hf 22 (by decide)).trans hp) ((hf 23 (by decide)).trans htmp)
    ((hf 24 (by decide)).trans hcounter) ((hf 25 (by decide)).trans hlatch)
    ((hf 26 (by decide)).trans hscratch) ((hf 27 (by decide)).trans hcopy)
  obtain ⟨out, hcall, hout, hregs, hbound⟩ := lift_checker_resources localChecker 21 25
    prepared small hrun hrestore hb hspace
  refine ⟨n + 1, out, ?_, hcall, ?_, hout, hbound⟩
  · unfold matrixCheckTime
    omega
  · simpa only [hregs] using haccept

theorem graph_matrix_candidate_valid {D r : ℕ} (s : Fin D → Cayley.Cube r)
    (q : ℕ) (qbits Dbits : List Bool)
    (hqv : BinaryArithmetic.toNat qbits = q) (hDv : BinaryArithmetic.toNat Dbits = D)
    (xs : List (Bool × Bool))
    (hfields : xs.map CodeCandidates.digitBits = CodeCandidates.matrixWords s)
    (hvalid : xs.any (CodeCandidates.invalidDigit false) = false)
    (a : MatrixState) (A : ℕ) (ha : ∀ i, (a.stacks i).length ≤ A)
    (he : ∀ i : Fin 29, a.stacks (Fin.castAdd 19 i) = [])
    (ht : a.stacks 30 = List.replicate D true) (hq : a.stacks 31 = qbits) (hDbits : a.stacks 32 = Dbits)
    (hr : a.stacks 33 = List.replicate r true)
    (hp : a.stacks 34 = []) (htmp : a.stacks 35 = []) (hcounter : a.stacks 36 = [])
    (hlatch : a.stacks 37 = []) (hscratch : a.stacks 38 = []) (hcopy : a.stacks 39 = [])
    (hcurrent : a.stacks 40 = CodeCandidates.tupleBits xs)
    (hinput : a.stacks 43 = []) (hpayload : a.stacks 44 = []) (houtertmp : a.stacks 45 = []) :
    ∃ n out, n ≤ matrixCheckTime A (D * r) r (graphCallbackBudget D r qbits.length Dbits.length)
        (graphStreamBudget D r qbits.length Dbits.length) + 2 * A + 73 * (D * r) + 23 ∧
      Eval graphMatrixCandidate n a out ∧
      (out.regs 15 = true ↔ WalshExistence.Good q s) ∧
      out.stacks = Function.update a.stacks 29 (matrixFrames s) ∧
      (∀ k c, k ≤ n → Trace (compiled graphMatrixCandidate 40 42) k
        (a.withPC (some (compiled graphMatrixCandidate 40 42).entry)) c →
        ∀ i, (c.stacks i).length ≤ max (3 * A + 73 * (D * r) + 23)
          (matrixCheckSpace A (D * r) r (graphCallbackBudget D r qbits.length Dbits.length))) := by
  have hlen : xs.length = D * r := by simpa [CodeCandidates.matrixWords] using congrArg List.length hfields
  have hword := pair_matrix_frames_eq xs s hfields
  have hwordlen : (matrixFrames s).length = 5 * (D * r) := by
    rw [← hword, CodeCandidates.scalarFrames_length, hlen]
  have result := matrix_candidate_valid false 29 graphChecker 33 37
      (by decide) (by decide) xs (matrixFrames s) hword a A
      (matrixCheckTime A (D * r) r (graphCallbackBudget D r qbits.length Dbits.length)
        (graphStreamBudget D r qbits.length Dbits.length))
      (matrixCheckSpace A (D * r) r (graphCallbackBudget D r qbits.length Dbits.length))
      (WalshExistence.Good q s) ha hcurrent hinput hpayload houtertmp hvalid
  rw [hlen] at result
  apply result
  intro prepared hprepared
  have hf (i : Fin 48) (hi : i ≠ 29) : prepared.stacks i = a.stacks i := by
    rw [hprepared, Function.update_of_ne hi]
  have hb : ∀ i, (prepared.stacks i).length ≤ A + 5 * (D * r) := by
    simpa [hwordlen] using updated_matrix_bound a prepared A 29 (matrixFrames s) ha hprepared
  have he' : GraphWorkEmpty (projectState id graphStreamStacks (projectState id checkerPorts prepared)) := by
    intro i
    apply (hf (Fin.castAdd 19 i) ?_).trans (he i)
    intro h
    have hv := congrArg Fin.val h
    change i.val = 29 at hv
    omega
  have hm : (projectState id checkerPorts prepared).stacks 29 = matrixFrames s := by
    change prepared.stacks 29 = _
    rw [hprepared, Function.update_self]
  obtain ⟨n, small, hrun, hn, haccept, hrestore, hspace⟩ := graph_checker_runs s q qbits Dbits hqv hDv
    (projectState id checkerPorts prepared) (A + 5 * (D * r)) (fun i => hb (checkerPorts i)) he' hm
    ((hf 30 (by decide)).trans ht) ((hf 31 (by decide)).trans hq) ((hf 32 (by decide)).trans hDbits)
    ((hf 33 (by decide)).trans hr) ((hf 34 (by decide)).trans hp) ((hf 35 (by decide)).trans htmp)
    ((hf 36 (by decide)).trans hcounter) ((hf 37 (by decide)).trans hlatch)
    ((hf 38 (by decide)).trans hscratch) ((hf 39 (by decide)).trans hcopy)
  obtain ⟨out, hcall, hout, hregs, hbound⟩ := lift_checker_resources graphChecker 33 37
    prepared small hrun hrestore hb hspace
  refine ⟨n + 1, out, ?_, hcall, ?_, hout, hbound⟩
  · unfold matrixCheckTime
    omega
  · simpa only [hregs] using haccept

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

structure LocalMatrixReady (t D d : ℕ) (a : MatrixState) : Prop where
  work : ∀ i : Fin 18, a.stacks (Fin.castAdd 30 i) = []
  rows : a.stacks 19 = List.replicate t true
  distance : a.stacks 20 = List.replicate d true
  dimension : a.stacks 21 = List.replicate D true
  payload : a.stacks 22 = []
  scratch : a.stacks 23 = []
  counter : a.stacks 24 = []
  latch : a.stacks 25 = []
  counterScratch : a.stacks 26 = []
  copy : a.stacks 27 = []
  outerInput : a.stacks 43 = []
  outerPayload : a.stacks 44 = []
  outerScratch : a.stacks 45 = []

structure GraphMatrixReady (D r : ℕ) (qbits Dbits : List Bool) (a : MatrixState) : Prop where
  work : ∀ i : Fin 29, a.stacks (Fin.castAdd 19 i) = []
  degree : a.stacks 30 = List.replicate D true
  quotient : a.stacks 31 = qbits
  degreeBits : a.stacks 32 = Dbits
  dimension : a.stacks 33 = List.replicate r true
  payload : a.stacks 34 = []
  scratch : a.stacks 35 = []
  counter : a.stacks 36 = []
  latch : a.stacks 37 = []
  counterScratch : a.stacks 38 = []
  copy : a.stacks 39 = []
  outerInput : a.stacks 43 = []
  outerPayload : a.stacks 44 = []
  outerScratch : a.stacks 45 = []

theorem LocalMatrixReady.of_frame {t D d : ℕ} {a b : MatrixState}
    (ha : LocalMatrixReady t D d a) (hf : ∀ i, i ≠ 18 → b.stacks i = a.stacks i) :
    LocalMatrixReady t D d b := by
  refine ⟨?_, (hf 19 (by decide)).trans ha.rows, (hf 20 (by decide)).trans ha.distance,
    (hf 21 (by decide)).trans ha.dimension, (hf 22 (by decide)).trans ha.payload,
    (hf 23 (by decide)).trans ha.scratch, (hf 24 (by decide)).trans ha.counter,
    (hf 25 (by decide)).trans ha.latch, (hf 26 (by decide)).trans ha.counterScratch,
    (hf 27 (by decide)).trans ha.copy, (hf 43 (by decide)).trans ha.outerInput,
    (hf 44 (by decide)).trans ha.outerPayload, (hf 45 (by decide)).trans ha.outerScratch⟩
  intro i
  apply (hf _ ?_).trans (ha.work i)
  intro h
  have hv := congrArg Fin.val h
  change i.val = 18 at hv
  omega

theorem GraphMatrixReady.of_frame {D r : ℕ} {qbits Dbits : List Bool} {a b : MatrixState}
    (ha : GraphMatrixReady D r qbits Dbits a) (hf : ∀ i, i ≠ 29 → b.stacks i = a.stacks i) :
    GraphMatrixReady D r qbits Dbits b := by
  refine ⟨?_, (hf 30 (by decide)).trans ha.degree, (hf 31 (by decide)).trans ha.quotient,
    (hf 32 (by decide)).trans ha.degreeBits, (hf 33 (by decide)).trans ha.dimension,
    (hf 34 (by decide)).trans ha.payload, (hf 35 (by decide)).trans ha.scratch,
    (hf 36 (by decide)).trans ha.counter, (hf 37 (by decide)).trans ha.latch,
    (hf 38 (by decide)).trans ha.counterScratch, (hf 39 (by decide)).trans ha.copy,
    (hf 43 (by decide)).trans ha.outerInput, (hf 44 (by decide)).trans ha.outerPayload,
    (hf 45 (by decide)).trans ha.outerScratch⟩
  intro i
  apply (hf _ ?_).trans (ha.work i)
  intro h
  have hv := congrArg Fin.val h
  change i.val = 29 at hv
  omega

theorem LocalMatrixReady.frame {t D d : ℕ} {a b : MatrixState}
    (ha : LocalMatrixReady t D d a) (hf : ∀ i, i ≠ 18 → i ≠ 40 → i ≠ 41 → i ≠ 42 → b.stacks i = a.stacks i) :
    LocalMatrixReady t D d b := by
  refine ⟨?_, (hf 19 (by decide) (by decide) (by decide) (by decide)).trans ha.rows, (hf 20 (by decide) (by decide) (by decide) (by decide)).trans ha.distance,
    (hf 21 (by decide) (by decide) (by decide) (by decide)).trans ha.dimension, (hf 22 (by decide) (by decide) (by decide) (by decide)).trans ha.payload,
    (hf 23 (by decide) (by decide) (by decide) (by decide)).trans ha.scratch, (hf 24 (by decide) (by decide) (by decide) (by decide)).trans ha.counter,
    (hf 25 (by decide) (by decide) (by decide) (by decide)).trans ha.latch, (hf 26 (by decide) (by decide) (by decide) (by decide)).trans ha.counterScratch,
    (hf 27 (by decide) (by decide) (by decide) (by decide)).trans ha.copy, (hf 43 (by decide) (by decide) (by decide) (by decide)).trans ha.outerInput,
    (hf 44 (by decide) (by decide) (by decide) (by decide)).trans ha.outerPayload, (hf 45 (by decide) (by decide) (by decide) (by decide)).trans ha.outerScratch⟩
  intro i
  apply (hf (Fin.castAdd 30 i) ?_ ?_ ?_ ?_).trans (ha.work i)
  · intro h
    have hv := congrArg Fin.val h
    change i.val = 18 at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    change i.val = 40 at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    change i.val = 41 at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    change i.val = 42 at hv
    omega

theorem GraphMatrixReady.frame {D r : ℕ} {qbits Dbits : List Bool} {a b : MatrixState}
    (ha : GraphMatrixReady D r qbits Dbits a) (hf : ∀ i, i ≠ 29 → i ≠ 40 → i ≠ 41 → i ≠ 42 → b.stacks i = a.stacks i) :
    GraphMatrixReady D r qbits Dbits b := by
  refine ⟨?_, (hf 30 (by decide) (by decide) (by decide) (by decide)).trans ha.degree, (hf 31 (by decide) (by decide) (by decide) (by decide)).trans ha.quotient,
    (hf 32 (by decide) (by decide) (by decide) (by decide)).trans ha.degreeBits, (hf 33 (by decide) (by decide) (by decide) (by decide)).trans ha.dimension,
    (hf 34 (by decide) (by decide) (by decide) (by decide)).trans ha.payload, (hf 35 (by decide) (by decide) (by decide) (by decide)).trans ha.scratch,
    (hf 36 (by decide) (by decide) (by decide) (by decide)).trans ha.counter, (hf 37 (by decide) (by decide) (by decide) (by decide)).trans ha.latch,
    (hf 38 (by decide) (by decide) (by decide) (by decide)).trans ha.counterScratch, (hf 39 (by decide) (by decide) (by decide) (by decide)).trans ha.copy,
    (hf 43 (by decide) (by decide) (by decide) (by decide)).trans ha.outerInput, (hf 44 (by decide) (by decide) (by decide) (by decide)).trans ha.outerPayload,
    (hf 45 (by decide) (by decide) (by decide) (by decide)).trans ha.outerScratch⟩
  intro i
  apply (hf (Fin.castAdd 19 i) ?_ ?_ ?_ ?_).trans (ha.work i)
  · intro h
    have hv := congrArg Fin.val h
    change i.val = 29 at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    change i.val = 40 at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    change i.val = 41 at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    change i.val = 42 at hv
    omega

def candidateBudget (A matrixDimension wordDimension callbackCost streamCost : ℕ) : ℕ :=
  matrixCheckTime A matrixDimension wordDimension callbackCost streamCost +
    2 * A + 73 * matrixDimension + 23

def candidateSpace (A matrixDimension wordDimension callbackCost : ℕ) : ℕ :=
  max (3 * A + 73 * matrixDimension + 23)
    (matrixCheckSpace A matrixDimension wordDimension callbackCost)

/-- Every current outer-counter tuple is processed by the actual local matrix
command, including invalid scalar digits and losing code candidates. -/
theorem local_matrix_candidate_runs (t D d : ℕ) (a : MatrixState) (A : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ A) (hcap : 5 * (t * D) ≤ A)
    (hready : LocalMatrixReady t D d a) (words : List (List Bool))
    (hshape : words.map List.length = List.replicate (t * D) 2)
    (hcurrent : a.stacks 40 = Encoding.encodeList id words) :
    ∃ n out, n ≤ candidateBudget A (t * D) D (callbackBudget t D d) (localStreamBudget t D d) ∧
      Eval localMatrixCandidate n a out ∧ LocalMatrixReady t D d out ∧
      (∀ i, i ≠ 18 → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ A) ∧
      (out.regs 15 = true → ∃ Q : Fin t → Fin D → SparseCode.F3,
        out.stacks 18 = matrixFrames Q ∧ SparseCode.HasDistance Q d) ∧
      (∀ k c, k ≤ n → Trace (compiled localMatrixCandidate 40 42) k
        (a.withPC (some (compiled localMatrixCandidate 40 42).entry)) c →
        ∀ i, (c.stacks i).length ≤ candidateSpace A (t * D) D (callbackBudget t D d)) := by
  obtain ⟨xs, hlen, hwords⟩ := CodeCandidates.pairs_of_shape words (t * D) hshape
  have hc : a.stacks 40 = CodeCandidates.tupleBits xs := by rw [hcurrent, tupleBits_eq, hwords]
  cases hvalid : xs.any (CodeCandidates.invalidDigit true) with
  | false =>
    obtain ⟨Q, hQ⟩ := CodeCandidates.ternary_matrix_digits_sound xs t D hlen hvalid
    obtain ⟨n, out, hn, hr, haccept, hout, hspace⟩ := local_matrix_candidate_valid Q d xs hQ hvalid a A
      ha hready.work hready.rows hready.distance hready.dimension hready.payload hready.scratch
      hready.counter hready.latch hready.counterScratch hready.copy hc
      hready.outerInput hready.outerPayload hready.outerScratch
    have hf : ∀ i, i ≠ 18 → out.stacks i = a.stacks i := by
      intro i hi
      rw [hout, Function.update_of_ne hi]
    refine ⟨n, out, hn, hr, hready.of_frame hf, hf, ?_, ?_, hspace⟩
    · intro i
      by_cases hi : i = 18
      · subst i
        rw [hout, Function.update_self, ← pair_matrix_frames_eq xs Q hQ,
          CodeCandidates.scalarFrames_length, hlen]
        exact hcap
      · rw [hf i hi]
        exact ha i
    · intro hy
      refine ⟨Q, ?_, haccept.mp hy⟩
      rw [hout, Function.update_self]
  | true =>
    obtain ⟨out, hr, hfalse, hout, hspace⟩ := matrix_candidate_invalid true 18 localChecker 21 25
      xs a A ha hc hready.outerInput hready.outerPayload hready.outerScratch hvalid
    have hf : ∀ i, i ≠ 18 → out.stacks i = a.stacks i := fun i _ => congrFun hout i
    refine ⟨68 * xs.length + 21, out, ?_, hr, hready.of_frame hf, hf, ?_, ?_, ?_⟩
    · unfold candidateBudget
      rw [hlen]
      omega
    · simpa only [hout] using ha
    · simp [hfalse]
    · intro k c hk ht i
      have hb := hspace k c hk ht i
      rw [hlen] at hb
      exact (by omega : (c.stacks i).length ≤ 3 * A + 73 * (t * D) + 23).trans
        (Nat.le_max_left _ _)

/-- The graph search likewise processes every current two-bit matrix tuple;
the only accepted physical matrix satisfies the actual Walsh checks. -/
theorem graph_matrix_candidate_runs (D r q : ℕ) (qbits Dbits : List Bool)
    (hqv : BinaryArithmetic.toNat qbits = q) (hDv : BinaryArithmetic.toNat Dbits = D)
    (a : MatrixState) (A : ℕ) (ha : ∀ i, (a.stacks i).length ≤ A) (hcap : 5 * (D * r) ≤ A)
    (hready : GraphMatrixReady D r qbits Dbits a) (words : List (List Bool))
    (hshape : words.map List.length = List.replicate (D * r) 2)
    (hcurrent : a.stacks 40 = Encoding.encodeList id words) :
    ∃ n out, n ≤ candidateBudget A (D * r) r (graphCallbackBudget D r qbits.length Dbits.length)
        (graphStreamBudget D r qbits.length Dbits.length) ∧
      Eval graphMatrixCandidate n a out ∧ GraphMatrixReady D r qbits Dbits out ∧
      (∀ i, i ≠ 29 → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ A) ∧
      (out.regs 15 = true → ∃ s : Fin D → Cayley.Cube r,
        out.stacks 29 = matrixFrames s ∧ WalshExistence.Good q s) ∧
      (∀ k c, k ≤ n → Trace (compiled graphMatrixCandidate 40 42) k
        (a.withPC (some (compiled graphMatrixCandidate 40 42).entry)) c →
        ∀ i, (c.stacks i).length ≤ candidateSpace A (D * r) r
          (graphCallbackBudget D r qbits.length Dbits.length)) := by
  obtain ⟨xs, hlen, hwords⟩ := CodeCandidates.pairs_of_shape words (D * r) hshape
  have hc : a.stacks 40 = CodeCandidates.tupleBits xs := by rw [hcurrent, tupleBits_eq, hwords]
  cases hvalid : xs.any (CodeCandidates.invalidDigit false) with
  | false =>
    obtain ⟨s, hs⟩ := CodeCandidates.binary_matrix_digits_sound xs D r hlen hvalid
    obtain ⟨n, out, hn, hr, haccept, hout, hspace⟩ := graph_matrix_candidate_valid s q qbits Dbits
      hqv hDv xs hs hvalid a A ha hready.work hready.degree hready.quotient hready.degreeBits
      hready.dimension hready.payload hready.scratch hready.counter hready.latch
      hready.counterScratch hready.copy hc hready.outerInput hready.outerPayload hready.outerScratch
    have hf : ∀ i, i ≠ 29 → out.stacks i = a.stacks i := by
      intro i hi
      rw [hout, Function.update_of_ne hi]
    refine ⟨n, out, hn, hr, hready.of_frame hf, hf, ?_, ?_, hspace⟩
    · intro i
      by_cases hi : i = 29
      · subst i
        rw [hout, Function.update_self, ← pair_matrix_frames_eq xs s hs,
          CodeCandidates.scalarFrames_length, hlen]
        exact hcap
      · rw [hf i hi]
        exact ha i
    · intro hy
      refine ⟨s, ?_, haccept.mp hy⟩
      rw [hout, Function.update_self]
  | true =>
    obtain ⟨out, hr, hfalse, hout, hspace⟩ := matrix_candidate_invalid false 29 graphChecker 33 37
      xs a A ha hc hready.outerInput hready.outerPayload hready.outerScratch hvalid
    have hf : ∀ i, i ≠ 29 → out.stacks i = a.stacks i := fun i _ => congrFun hout i
    refine ⟨68 * xs.length + 21, out, ?_, hr, hready.of_frame hf, hf, ?_, ?_, ?_⟩
    · unfold candidateBudget
      rw [hlen]
      omega
    · simpa only [hout] using ha
    · simp [hfalse]
    · intro k c hk ht i
      have hb := hspace k c hk ht i
      rw [hlen] at hb
      exact (by omega : (c.stacks i).length ≤ 3 * A + 73 * (D * r) + 23).trans
        (Nat.le_max_left _ _)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

/-- The streamed checker's retained workspace is a fixed linear polynomial
in its input words, dimensions, and one arithmetic callback budget. -/
theorem candidateSpace_le (A matrixDimension wordDimension callbackCost : ℕ) :
    candidateSpace A matrixDimension wordDimension callbackCost ≤
      20000 * (A + matrixDimension + wordDimension + callbackCost + 1) := by
  have hc : coreSpace (A + 5 * matrixDimension) wordDimension callbackCost ≤
      300 * (A + matrixDimension + wordDimension + callbackCost + 1) := by
    unfold coreSpace
    apply max_le <;> omega
  unfold candidateSpace matrixCheckSpace
  apply max_le
  · omega
  · apply max_le <;> omega

/-- New staging, validation, and complete inner checking add only a fixed
linear factor to the explicit original arithmetic and word-scan budget. -/
theorem candidateBudget_le (A matrixDimension wordDimension callbackCost streamCost : ℕ) :
    candidateBudget A matrixDimension wordDimension callbackCost streamCost ≤
      1000 * (A + matrixDimension + wordDimension + callbackCost + streamCost + 1) := by
  have hc : coreSpace (A + 5 * matrixDimension) wordDimension callbackCost ≤
      300 * (A + matrixDimension + wordDimension + callbackCost + 1) := by
    unfold coreSpace
    apply max_le <;> omega
  unfold candidateBudget matrixCheckTime
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
