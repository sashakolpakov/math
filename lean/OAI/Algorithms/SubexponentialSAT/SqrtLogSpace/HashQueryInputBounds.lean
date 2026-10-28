import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyExecution
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedQueryAdapter
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassSpace

/-! Physical input bounds for all attained greedy histories and every trial,
including losing candidates. All bounds concern literal retained words and
raw slots. No execution-time or successful-query bound is used. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryInputBounds

open BitProgram StructuredCalls SqrtLog
open HashGreedyProgram HashGreedyCNF HashGreedyCode

/-- The original serializer retains all slots, including repeats and zeros. -/
theorem initial_bytes {m B : ℕ} (shifts : SparseCode.SuppliedShifts m B)
    (Q : SparseCode.SuppliedLocal m B) :
    (encodedHistory (initial shifts Q)).length ≤ SparseCode.totalRows m B *
      (2 * (SparseCode.degreeBound m B * HashCandidates.digitWidth m) + 2) + 1 := by
  have h := encodedHistory_length_le (initial shifts Q)
    (SparseCode.degreeBound m B * HashCandidates.digitWidth m) (by
      intro bits hb
      obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hb
      rw [List.length_reverse, CodeRowsProgram.rowPayload_length]
      exact Nat.mul_le_mul_right _ (CodeRowsProgram.serializedRows_supplied_slots shifts Q row hr))
  simpa only [HashGreedyCode.initial, LeafScopeResourceBounds.initialPayloads, List.length_map,
    CodeRowsProgram.serializedRows_supplied_length] using h

theorem history_bytes {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (depth : ℕ) (start : List (List Bool)) (rounds : ℕ) :
    (encodedHistory (history clauses depth start rounds)).length ≤
      (encodedHistory start).length + rounds * (2 * HashCandidates.payloadWidth m depth + 2) := by
  exact HashGreedyRound.encodedHistory_iter_length_le (entry clauses depth)
    (HashSelect.loopCap n m) (HashCandidates.payloadWidth m depth) rounds start
    (fun rows _ rank _ => HashGreedyCandidate.entry_fits _ _ n m depth rows rank) rounds le_rfl

@[simp] theorem trial_bytes (payload : List Bool) (rows : List (List Bool)) :
    (encodedHistory (payload :: rows)).length =
      (encodedHistory rows).length + 2 * payload.length + 2 := by
  simp only [encodedHistory, List.map_cons, Encoding.encodeList, id_eq, List.length_cons,
    List.length_append, Encoding.length_frame, List.length_reverse]
  omega

/-- A common cap on actual scalar parameters gives one fixed cube for all
initial, attained, and trial history streams. The index rank is unrestricted. -/
theorem serialized_bounds {n m B : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (S : ℕ) (hS : 1 ≤ S) (hrows : SparseCode.totalRows m B ≤ S)
    (hdegree : SparseCode.degreeBound m B ≤ S) (hdepth : SparseCode.distanceDenom m B ≤ S)
    (hwidth : HashCandidates.digitWidth m ≤ S) (hrounds : HashSelect.loopCap n m ≤ S)
    (rounds rank : ℕ) (hq : rounds ≤ HashSelect.loopCap n m) :
    (encodedHistory (initial shifts Q)).length ≤ 5 * S ^ 3 ∧
      (encodedHistory (history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds)).length
        ≤ 9 * S ^ 3 ∧
      (HashGreedyCandidate.candidate m (SparseCode.distanceDenom m B) rank).length ≤ S ^ 2 ∧
      (encodedHistory (HashGreedyCandidate.candidate m (SparseCode.distanceDenom m B) rank ::
        history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds)).length ≤ 16 * S ^ 3 := by
  have hS3 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) S
  have h23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by decide)
  have h13 : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ hS
  have hDW : SparseCode.degreeBound m B * HashCandidates.digitWidth m ≤ S ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hdegree hwidth
  have hC : HashCandidates.payloadWidth m (SparseCode.distanceDenom m B) ≤ S ^ 2 := by
    simpa only [HashCandidates.payloadWidth, pow_two] using Nat.mul_le_mul hdepth hwidth
  have hi := initial_bytes shifts Q
  have hi' : (encodedHistory (initial shifts Q)).length ≤ 5 * S ^ 3 := by
    have hp := Nat.mul_le_mul hrows (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hDW) 2)
    nlinarith only [hi, hp, hS3, h13]
  have hh := history_bytes clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds
  have hh' : (encodedHistory (history clauses (SparseCode.distanceDenom m B)
      (initial shifts Q) rounds)).length ≤ 9 * S ^ 3 := by
    have hp := Nat.mul_le_mul (hq.trans hrounds) (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hC) 2)
    nlinarith only [hh, hi', hp, hS3]
  refine ⟨hi', hh', ?_, ?_⟩
  · simpa only [HashGreedyCandidate.candidate_length] using hC
  · rw [trial_bytes, HashGreedyCandidate.candidate_length]
    nlinarith only [hh', hC, h23, h13]

/-- The explicit allowance required by the actual outer-run theorem, not
merely a bound on the length of an individual attained history. -/
theorem history_budget {n m B : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (S : ℕ) (hS : 1 ≤ S) (hrows : SparseCode.totalRows m B ≤ S)
    (hdegree : SparseCode.degreeBound m B ≤ S) (hdepth : SparseCode.distanceDenom m B ≤ S)
    (hwidth : HashCandidates.digitWidth m ≤ S) (hrounds : HashSelect.loopCap n m ≤ S) :
    (encodedHistory (initial shifts Q)).length + HashSelect.loopCap n m *
      (2 * HashCandidates.payloadWidth m (SparseCode.distanceDenom m B) + 2) ≤ 9 * S ^ 3 := by
  have hi := (serialized_bounds clauses shifts Q S hS hrows hdegree hdepth hwidth hrounds 0 0
    (Nat.zero_le _)).1
  have hC : HashCandidates.payloadWidth m (SparseCode.distanceDenom m B) ≤ S ^ 2 := by
    simpa only [HashCandidates.payloadWidth, pow_two] using Nat.mul_le_mul hdepth hwidth
  have hS3 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) S
  have hp := Nat.mul_le_mul hrounds (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hC) 2)
  nlinarith only [hi, hp, hS3]

theorem reference_bytes (m S : ℕ) (hS : 1 ≤ S) (hm : m ≤ S) :
    (Encoding.encodeList id (RowSelectionProgram.Index.alphabet m)).length ≤ 5 * S ^ 2 := by
  have h := Encoding.length_encodeList_upper id (RowSelectionProgram.Index.alphabet m) m
    (HashMassBounds.reference_length m)
  rw [RowSelectionProgram.Index.alphabet_length] at h
  have hp := Nat.mul_le_mul (show 2 * m + 2 ≤ 2 * S + 2 by omega) hm
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by decide) S
  nlinarith only [h, hp, hS, hS2]

theorem accumulator_growth (n m S : ℕ) (_hS : 1 ≤ S) (hn : n ≤ S) (hm : m ≤ S) :
    HashMassAdapter.outputGrowth (fun _ => n + 1) (RowSelectionProgram.Index.alphabet m) ≤ 3 * S ^ 2 := by
  have h := HashMassAdapter.outputGrowth_le (fun _ => n + 1) (RowSelectionProgram.Index.alphabet m)
    (n + 1) (fun _ _ => le_rfl)
  rw [RowSelectionProgram.Index.alphabet_length] at h
  have hp := Nat.mul_le_mul hm (show n + 1 + 1 ≤ S + 2 by omega)
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by decide) S
  nlinarith only [h, hp, hS2]

/-- One actual retained allowance L=16*S³ discharges all numeric premises of
RunSpace, including the complete reference stream and full mass accumulator. -/
theorem run_caps {n m B : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (S : ℕ) (hS : 1 ≤ S) (hn : n ≤ S) (hm : m ≤ S)
    (hrows : SparseCode.totalRows m B ≤ S) (hdegree : SparseCode.degreeBound m B ≤ S)
    (hdepth : SparseCode.distanceDenom m B ≤ S) (hwidth : HashCandidates.digitWidth m ≤ S)
    (hrounds : HashSelect.loopCap n m ≤ S) :
    let L := 16 * S ^ 3
    HashSelect.loopCap n m ≤ L ∧ HashCandidates.payloadWidth m (SparseCode.distanceDenom m B) ≤ L ∧
      2 * HashCandidates.payloadWidth m (SparseCode.distanceDenom m B) + 3 ≤ L ∧
      (encodedHistory (initial shifts Q)).length + HashSelect.loopCap n m *
        (2 * HashCandidates.payloadWidth m (SparseCode.distanceDenom m B) + 2) ≤ L ∧
      (Encoding.encodeList id (RowSelectionProgram.Index.alphabet m)).length ≤ L ∧
      HashMassAdapter.outputGrowth (fun _ => n + 1) (RowSelectionProgram.Index.alphabet m) ≤ L ∧
      n + 1 ≤ L := by
  dsimp only
  have hhist := history_budget clauses shifts Q S hS hrows hdegree hdepth hwidth hrounds
  have href := reference_bytes m S hS hm
  have hgrowth := accumulator_growth n m S hS hn hm
  have hC : HashCandidates.payloadWidth m (SparseCode.distanceDenom m B) ≤ S ^ 2 := by
    simpa only [HashCandidates.payloadWidth, pow_two] using Nat.mul_le_mul hdepth hwidth
  have hS3 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) S
  have h23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by decide)
  have h13 : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ hS
  omega

/-- All persistent boundary words are covered, including the incumbent,
odometer, remaining outer counter and the full attained history. -/
theorem boundary_words {n m B : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (S : ℕ) (hS : 1 ≤ S) (hrows : SparseCode.totalRows m B ≤ S)
    (hdegree : SparseCode.degreeBound m B ≤ S) (hdepth : SparseCode.distanceDenom m B ≤ S)
    (hwidth : HashCandidates.digitWidth m ≤ S) (hrounds : HashSelect.loopCap n m ≤ S)
    (base d : State 40 896) (hbase : ∀ i, (base.stacks i).length ≤ S)
    (rounds : ℕ) (hq : rounds ≤ HashSelect.loopCap n m)
    (word : List Bool) (hword : word.length = HashCandidates.payloadWidth m (SparseCode.distanceDenom m B))
    (hframe : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
      d.stacks i = base.stacks i)
    (hscore : (d.stacks 771).length ≤ HashSelect.loopCap n m)
    (hpayload : (d.stacks 770).length ≤ HashCandidates.payloadWidth m (SparseCode.distanceDenom m B))
    (hhistory : d.stacks 777 = encodedHistory
      (history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds))
    (hcounter : d.stacks 778 = Encoding.encodeList id [word])
    (hscratch : d.stacks 779 = []) (houter : (d.stacks 781).length ≤ HashSelect.loopCap n m) :
    ∀ i, (d.stacks i).length ≤ 16 * S ^ 3 := by
  have hb := serialized_bounds clauses shifts Q S hS hrows hdegree hdepth hwidth hrounds rounds 0 hq
  have hC : HashCandidates.payloadWidth m (SparseCode.distanceDenom m B) ≤ S ^ 2 := by
    simpa only [HashCandidates.payloadWidth, pow_two] using Nat.mul_le_mul hdepth hwidth
  have h23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by decide)
  have h13 : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ hS
  have hS3 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) S
  intro i
  by_cases h770 : i = 770
  · subst i; omega
  by_cases h771 : i = 771
  · subst i; omega
  by_cases h777 : i = 777
  · subst i; rw [hhistory]; omega
  by_cases h778 : i = 778
  · subst i
    rw [hcounter]
    simp only [Encoding.encodeList, id_eq, Encoding.length_frame, List.length_cons,
      List.length_nil, List.length_append, hword]
    omega
  by_cases h779 : i = 779
  · subst i; simp [hscratch]
  by_cases h781 : i = 781
  · subst i; omega
  rw [hframe i h770 h771 h777 h778 h779 h781]
  exact (hbase i).trans (by omega)

/-- Time callbacks need only the physically read source words. Unrelated
incumbents need no artificial cap here; prefix space uses boundary_words. -/
theorem staged_source_words {n m B : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (S : ℕ) (hS : 1 ≤ S) (hrows : SparseCode.totalRows m B ≤ S)
    (hdegree : SparseCode.degreeBound m B ≤ S) (hdepth : SparseCode.distanceDenom m B ≤ S)
    (hwidth : HashCandidates.digitWidth m ≤ S) (hrounds : HashSelect.loopCap n m ≤ S)
    (d : State 40 896) (rounds : ℕ) (hq : rounds ≤ HashSelect.loopCap n m)
    (hmasters : ∀ i ∈ ([782,783,784,785] : List (Fin 896)), (d.stacks i).length ≤ S)
    (hhistory : d.stacks 777 = encodedHistory
      (history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds))
    (word : List Bool) :
    ∀ i ∈ HashMassStaged.stagedPorts,
      ((LeafOuterNative.trialStaged
        (HashGreedyExecution.trialState d m (SparseCode.distanceDenom m B) word)).stacks i).length
          ≤ 16 * S ^ 3 := by
  let a := HashGreedyExecution.trialState d m (SparseCode.distanceDenom m B) word
  have hh := (serialized_bounds clauses shifts Q S hS hrows hdegree hdepth hwidth hrounds rounds 0 hq).2.1
  have hC : HashCandidates.payloadWidth m (SparseCode.distanceDenom m B) ≤ S ^ 2 := by
    simpa only [HashCandidates.payloadWidth, pow_two] using Nat.mul_le_mul hdepth hwidth
  have h23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by decide)
  have h13 : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ hS
  have hS3 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) S
  have hsrc := LeafOuterNative.trialStaged_sources a
  have hframe (i : Fin 896) (hi : i ≠ 768) : a.stacks i = d.stacks i := by
    simp only [a, HashGreedyExecution.trialState, Function.update_of_ne hi]
  intro i hi
  simp only [HashMassStaged.stagedPorts, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hsrc.1, hframe 784 (by decide)]
    exact (hmasters 784 (by simp)).trans (by omega)
  · rw [hsrc.2.1, hframe 777 (by decide), hhistory]
    have hp : (a.stacks 768).length = HashCandidates.payloadWidth m (SparseCode.distanceDenom m B) := by
      simp [a, HashGreedyExecution.trialState]
    simp only [List.length_cons, List.length_append, Encoding.length_frame, List.length_reverse, hp]
    omega
  · rw [show (LeafOuterNative.trialStaged a).stacks 702 = [] from LeafOuterNative.prefixed_scratch _]
    simp
  · rw [hsrc.2.2.1, hframe 782 (by decide)]
    exact (hmasters 782 (by simp)).trans (by omega)
  · rw [hsrc.2.2.2.1, hframe 783 (by decide)]
    exact (hmasters 783 (by simp)).trans (by omega)
  · rw [hsrc.2.2.2.2, hframe 785 (by decide)]
    exact (hmasters 785 (by simp)).trans (by omega)

/-- Literal native staging of any candidate, including a loser, obeys the
same fixed cap. Every stack is bounded, not only the six source ports. -/
theorem staged_words (d : State 40 896) (m depth S : ℕ) (hS : 1 ≤ S)
    (hd : ∀ i, (d.stacks i).length ≤ 16 * S ^ 3)
    (hdepth : depth ≤ S) (hwidth : HashCandidates.digitWidth m ≤ S) (word : List Bool) :
    ∀ i, ((LeafOuterNative.trialStaged (HashGreedyExecution.trialState d m depth word)).stacks i).length
      ≤ 50 * S ^ 3 := by
  have hC : HashCandidates.payloadWidth m depth ≤ S ^ 2 := by
    simpa only [HashCandidates.payloadWidth, pow_two] using Nat.mul_le_mul hdepth hwidth
  have h23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by decide)
  have h13 : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ hS
  have htrial : ∀ i, ((HashGreedyExecution.trialState d m depth word).stacks i).length ≤ 16 * S ^ 3 := by
    intro i
    by_cases hi : i = 768
    · subst i
      simp only [HashGreedyExecution.trialState, Function.update_self, HashCandidates.normalize_length]
      omega
    · simpa only [HashGreedyExecution.trialState, Function.update_of_ne hi] using hd i
  have hs := HashMassStaged.staged_stack_bound (HashGreedyExecution.trialState d m depth word)
    (16 * S ^ 3) htrial
  intro i
  have h := hs i
  omega

/-- One finite sum collects concrete numeric parameters and a physical
master-word allowance. Its definition contains no search or query time. -/
def commonCap (n m B wordBound : ℕ) : ℕ :=
  n + m + SparseCode.totalRows m B + SparseCode.degreeBound m B +
    SparseCode.distanceDenom m B + HashCandidates.digitWidth m + HashSelect.loopCap n m + wordBound + 1

theorem commonCap_bounds (n m B wordBound : ℕ) :
    1 ≤ commonCap n m B wordBound ∧ SparseCode.totalRows m B ≤ commonCap n m B wordBound ∧
      SparseCode.degreeBound m B ≤ commonCap n m B wordBound ∧
      SparseCode.distanceDenom m B ≤ commonCap n m B wordBound ∧
      HashCandidates.digitWidth m ≤ commonCap n m B wordBound ∧
      HashSelect.loopCap n m ≤ commonCap n m B wordBound ∧ wordBound ≤ commonCap n m B wordBound := by
  unfold commonCap
  omega

/-- Every actual trial source has one explicit fixed polynomial before any
round or candidate is selected; the history premise identifies the attained run. -/
theorem staged_sources_commonCap {n m B : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (wordBound : ℕ) (d : State 40 896) (rounds : ℕ) (hq : rounds ≤ HashSelect.loopCap n m)
    (hmasters : ∀ i ∈ ([782,783,784,785] : List (Fin 896)), (d.stacks i).length ≤ wordBound)
    (hhistory : d.stacks 777 = encodedHistory
      (history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds)) (word : List Bool) :
    ∀ i ∈ HashMassStaged.stagedPorts,
      ((LeafOuterNative.trialStaged
        (HashGreedyExecution.trialState d m (SparseCode.distanceDenom m B) word)).stacks i).length
          ≤ 16 * (commonCap n m B wordBound) ^ 3 := by
  obtain ⟨hS, hr, hd, hp, hw, hb, hword⟩ := commonCap_bounds n m B wordBound
  exact staged_source_words clauses shifts Q _ hS hr hd hp hw hb d rounds hq
    (fun i hi => (hmasters i hi).trans hword) hhistory word

/-- Exact source ports read by the marked frontend; 706 is its actual flag. -/
def querySourcePorts : List (Fin 896) := [700,701,705,706,707,708,709]

/-- The actual marker adapter restores699, creates the forward unary index705
and true flag706, and preserves all six physically staged source words. -/
theorem marked_source_words {m : ℕ} (a : State 40 896) (S : ℕ) (hS : 1 ≤ S) (hm : m ≤ S)
    (hstage : ∀ i ∈ HashMassStaged.stagedPorts, (a.stacks i).length ≤ 16 * S ^ 3)
    (e : Fin m) (href : a.stacks 321 = (Encoding.encodeNat e.val).reverse)
    (h699 : a.stacks 699 = []) (h705 : a.stacks 705 = []) (h706 : a.stacks 706 = []) :
    (HashMarkedQueryAdapter.markResult a).stacks 699 = [] ∧
      (HashMarkedQueryAdapter.markResult a).stacks 705 = Encoding.encodeNat e.val ∧
      (HashMarkedQueryAdapter.markResult a).stacks 706 = [true] ∧
      ∀ i ∈ querySourcePorts, ((HashMarkedQueryAdapter.markResult a).stacks i).length ≤ 16 * S ^ 3 := by
  have hout := HashMarkedQueryAdapter.markResult_stacks a h699 h705 h706
  have hS3 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) S
  have h13 : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ hS
  have he : e.val + 1 ≤ S := by have h := e.isLt; omega
  refine ⟨by simp [hout,h699], by simp [hout,href], by simp [hout], ?_⟩
  intro i hi
  by_cases hmark : i = 705
  · subst i
    simp only [hout, Function.update_of_ne (by decide : (705 : Fin 896) ≠ 706),
      Function.update_self, href, List.reverse_reverse, Encoding.length_encodeNat]
    omega
  by_cases hflag : i = 706
  · subst i
    simp only [hout, Function.update_self, List.length_cons, List.length_nil]
    omega
  have hsource : i ∈ HashMassStaged.stagedPorts := by
    simp only [querySourcePorts, HashMassStaged.stagedPorts, List.mem_cons,
      List.not_mem_nil, or_false] at *
    tauto
  simpa only [hout, Function.update_of_ne hflag, Function.update_of_ne hmark] using hstage i hsource

/-- The paid marker setup has a fixed polynomial prefix cap once the actual
caller words are bounded. Its time depends only on the current unary index. -/
theorem marker_input_prefix {m : ℕ} (a : State 40 896) (S : ℕ) (hS : 1 ≤ S) (hm : m ≤ S)
    (ha : ∀ i, (a.stacks i).length ≤ 50 * S ^ 3)
    (e : Fin m) (href : a.stacks 321 = (Encoding.encodeNat e.val).reverse)
    (h698 : a.stacks 698 = []) (h699 : a.stacks 699 = []) :
    ∃ steps ≤ 10 * S + 10,
      Eval HashMarkedQueryAdapter.markInput steps a (HashMarkedQueryAdapter.markResult a) ∧
      HashGreedyProgram.NativeRound.StageSpace HashMarkedQueryAdapter.markInput (steps + 1) a
        (50000 * S ^ 3) := by
  have he : (a.stacks 321).length ≤ S := by
    simp only [href, List.length_reverse, Encoding.length_encodeNat]
    have h := e.isLt
    omega
  have hS3 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) S
  have h13 : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ hS
  refine ⟨10 * (a.stacks 321).length + 10, by omega,
    HashMarkedQueryAdapter.markInput_eval a h698 h699, ?_⟩
  constructor
  intro k c hk hc i
  have h := StructuredSpace.local_stack_bound (compiled HashMarkedQueryAdapter.markInput 778 777)
    (StreamResources.dataBits_le_mul _ ha) k c hk hc i
  omega

/-- Parser construction changes only320/321. The full retained workspace
therefore identifies every physical query source even when322 is arbitrary. -/
theorem record_input_frame (staged a : State 40 896)
    (hready : HashMassAdapter.Ready (fun ws => ws = HashMassAdapter.workspace staged) a)
    (tail bits : List Bool) (i : Fin 896) (hi : 324 < i.val) :
    (RecordPrograms.state HashMassAdapter.recordPorts a false true false tail bits.reverse).stacks i =
      staged.stacks i := by
  have hneq (j : Fin 896) (hj : j.val ≤ 324) : i ≠ j := by
    intro h; subst i; omega
  have hf := HashMassAdapter.workspace_frame staged a hready.workspace_ready i
    (hneq 320 (by decide)) (hneq 321 (by decide)) (hneq 322 (by decide))
    (hneq 323 (by decide)) (hneq 324 (by decide))
  simpa only [RecordPrograms.state, HashMassAdapter.recordPorts,
    Function.update_of_ne (hneq 321 (by decide)),
    Function.update_of_ne (hneq 320 (by decide))] using hf

/-- Source-only transport into the actual collector callback. No hypothesis
restricts the retained accumulator or unread record stream. -/
theorem record_input_sources (staged a : State 40 896) (S : ℕ)
    (hready : HashMassAdapter.Ready (fun ws => ws = HashMassAdapter.workspace staged) a)
    (hstage : ∀ i ∈ HashMassStaged.stagedPorts, (staged.stacks i).length ≤ 16 * S ^ 3)
    (tail bits : List Bool) :
    ∀ i ∈ HashMassStaged.stagedPorts,
      ((RecordPrograms.state HashMassAdapter.recordPorts a false true false tail bits.reverse).stacks i).length
        ≤ 16 * S ^ 3 := by
  intro i hi
  have hhigh : 324 < i.val := by
    simp only [HashMassStaged.stagedPorts, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [record_input_frame staged a hready tail bits i hhigh]
  exact hstage i hi

/-- The actual markInput output inherits all staged source bounds from Ready;
its only new source is the actual finite reference and its true mark flag. -/
theorem record_marked_sources {m : ℕ} (staged a : State 40 896) (S : ℕ)
    (hS : 1 ≤ S) (hm : m ≤ S)
    (hready : HashMassAdapter.Ready (fun ws => ws = HashMassAdapter.workspace staged) a)
    (hstage : ∀ i ∈ HashMassStaged.stagedPorts, (staged.stacks i).length ≤ 16 * S ^ 3)
    (h699 : staged.stacks 699 = []) (h705 : staged.stacks 705 = []) (h706 : staged.stacks 706 = [])
    (tail : List Bool) (e : Fin m) :
    let input := RecordPrograms.state HashMassAdapter.recordPorts a false true false tail
      (Encoding.encodeNat e.val).reverse
    (HashMarkedQueryAdapter.markResult input).stacks 699 = [] ∧
      (HashMarkedQueryAdapter.markResult input).stacks 705 = Encoding.encodeNat e.val ∧
      (HashMarkedQueryAdapter.markResult input).stacks 706 = [true] ∧
      ∀ i ∈ querySourcePorts, ((HashMarkedQueryAdapter.markResult input).stacks i).length ≤ 16 * S ^ 3 := by
  dsimp only
  apply marked_source_words _ S hS hm
    (record_input_sources staged a S hready hstage tail (Encoding.encodeNat e.val)) e
  · simp [RecordPrograms.state, HashMassAdapter.recordPorts]
  · rw [record_input_frame staged a hready tail (Encoding.encodeNat e.val) 699 (by decide)]
    exact h699
  · rw [record_input_frame staged a hready tail (Encoding.encodeNat e.val) 705 (by decide)]
    exact h705
  · rw [record_input_frame staged a hready tail (Encoding.encodeNat e.val) 706 (by decide)]
    exact h706

/-- Space additionally charges the actual unread tail, current reference and
accumulator. The three caps are exactly those supplied by the collector's
prefix invariant when the outer retained allowance is16*S³. -/
theorem record_input_words (staged a : State 40 896) (S : ℕ) (hS : 1 ≤ S)
    (hstage : ∀ i, (staged.stacks i).length ≤ 50 * S ^ 3)
    (hready : HashMassAdapter.Ready (fun ws => ws = HashMassAdapter.workspace staged) a)
    (tail bits : List Bool)
    (hacc : (HashMassAdapter.read a).length ≤ 3 * (16 * S ^ 3) + 2)
    (htail : tail.length ≤ 3 * (16 * S ^ 3) + 2)
    (hbits : bits.length ≤ 3 * (16 * S ^ 3) + 2) :
    ∀ i, ((RecordPrograms.state HashMassAdapter.recordPorts a false true false tail bits.reverse).stacks i).length
      ≤ 50 * S ^ 3 := by
  have h13 : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ hS
  apply HashMassSpace.state_stack_bound
    (fun ws => ws = HashMassAdapter.workspace staged) (50 * S ^ 3) _
    a false true false tail bits.reverse hready.workspace_ready
  · omega
  · simp [hready.result_empty]
  · simp [hready.scratch_empty]
  · omega
  · simp only [List.length_reverse]
    omega
  · intro frame hframe i
    rw [hframe]
    exact hstage (HashMassAdapter.workPort i)

/-- Fixed-degree input substitution. Constants and degree are fixed before
any particular input or candidate is chosen. -/
theorem input_polynomial (S A degree inputLength : ℕ)
    (hS : S ≤ A * (inputLength + 1) ^ degree) :
    50 * S ^ 3 ≤ (50 * A ^ 3) * (inputLength + 1) ^ (3 * degree) := by
  have h := Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left hS 3)
  simpa only [mul_pow, ← pow_mul, Nat.mul_assoc, Nat.mul_comm degree 3] using h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryInputBounds
