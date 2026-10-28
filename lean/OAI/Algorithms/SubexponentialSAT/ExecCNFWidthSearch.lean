import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFTupleInitialize
import OAI.Algorithms.SubexponentialSAT.ExecSunflowerCallback

namespace OAI.Algorithms

/-!
# Concrete search through one width's candidate tuples

The callback below is the actual composed parser, index guard, family/core
builder, sunflower checker, and first-witness commit. Its aggregate arithmetic
budget is separate from the source execution and coverage proof.
-/

namespace SubexponentialSAT.ExecCNFWidthSearch

open BitProgram StructuredCalls
open ExecCNFTupleEnumeration

abbrev Data := State 32 32
abbrev Formula := ExecSunflowerCallback.Formula

def ports : Ports 32 32 where
  register := ⟨Fin.castAdd 29, Fin.castAdd_injective 3 29⟩
  counter := 17
  scratch := 18
  counter_ne_scratch := by decide

abbrev Invariant := ExecSunflowerCallback.Invariant

theorem invariant_stable (F : Formula) (limit width rows : List Bool) :
    CounterForPrograms.FrameStable ports (fun _ => Invariant F limit width rows) := by
  intro n a b hab ha hb21
  have transfer (i : Fin 32) (h17 : i ≠ 17) (h18 : i ≠ 18) :
      b.stacks i = a.stacks i := (hab i h17 h18).symm
  have ha21 : a.stacks 21 = [] := (hab 21 (by decide) (by decide)).trans hb21
  obtain ⟨hF, hl, hwork, hworkspace, hw, hr⟩ := ha ha21
  rcases hwork with ⟨hsmall, h8, h13, h22, h23, h24, h25, h26⟩
  refine ⟨(transfer 16 (by decide) (by decide)).trans hF,
    (transfer 19 (by decide) (by decide)).trans hl, ?_, ?_,
    (transfer 14 (by decide) (by decide)).trans hw,
    (transfer 15 (by decide) (by decide)).trans hr⟩
  · refine ⟨?_, (transfer 8 (by decide) (by decide)).trans h8,
      (transfer 13 (by decide) (by decide)).trans h13,
      (transfer 22 (by decide) (by decide)).trans h22,
      (transfer 23 (by decide) (by decide)).trans h23,
      (transfer 24 (by decide) (by decide)).trans h24,
      (transfer 25 (by decide) (by decide)).trans h25,
      (transfer 26 (by decide) (by decide)).trans h26⟩
    intro i
    apply (transfer (Fin.castAdd 25 i) ?_ ?_).trans (hsmall i)
    all_goals intro he; have hv := congrArg Fin.val he; simp at hv; omega
  · intro i hi
    apply (transfer (Fin.castAdd 19 i) ?_ ?_).trans (hworkspace i hi)
    all_goals intro he; have hv := congrArg Fin.val he; simp at hv; omega

def BodyBudget (F : Formula) (limit width rows : List Bool) (k r w budget : ℕ) : Prop :=
  ∀ (mask : List Bool) (indices : List (List Bool)),
    mask.length = k → indices.map List.length = List.replicate r w →
    ExecSunflowerCallback.bound F mask limit width rows indices ≤ budget

/-- The runtime premise ranges only over the arithmetic bound of the already
fixed callback. Its execution and state invariant are proved here. -/
theorem callback_spec (F : Formula) (limit width rows : List Bool) (k r w budget : ℕ)
    (hb : BodyBudget F limit width rows k r w budget) :
    BodySpec ports ExecSunflowerCallback.command (k :: List.replicate r w)
      (Invariant F limit width rows) budget := by
  intro tuple d hshape hi ht hs
  cases tuple with
  | nil => simp at hshape
  | cons mask indices =>
    have hm : mask.length = k := (List.cons.inj hshape).1
    have hw : indices.map List.length = List.replicate r w := (List.cons.inj hshape).2
    obtain ⟨n, hn, e, he, heS⟩ := ExecSunflowerCallback.command_eval
      F mask limit width rows indices d
      (ExecSunflowerCallback.fresh_of_invariant F mask limit width rows indices d hi ht)
    have hne : d.stacks 17 ≠ [] := by
      change d.stacks ports.counter ≠ []
      rw [ht]
      simp [Encoding.encodeList]
    refine ⟨n, e, hn.trans (hb mask indices hm hw), he, ?_, ?_, ?_⟩
    · change e.stacks 17 = _
      rw [heS, ExecSunflowerCallback.outputStacks_frame _ _ _ _ _ _ _ 17
        (by decide) (by decide) (by decide)]
      exact ht
    · change e.stacks 18 = []
      rw [heS, ExecSunflowerCallback.outputStacks_frame _ _ _ _ _ _ _ 18
        (by decide) (by decide) (by decide)]
      exact hs
    · exact ExecSunflowerCallback.invariant_preserved
        F mask limit width rows indices d e hi hne heS

theorem callback_output (F : Formula) (mask limit width rows : List Bool)
    (indices : List (List Bool)) (a b : Data) (n : ℕ)
    (hi : Invariant F limit width rows a)
    (ht : a.stacks 17 = Encoding.encodeList id (mask :: indices))
    (he : Eval ExecSunflowerCallback.command n a b) :
    b.stacks = ExecSunflowerCallback.outputStacks F mask limit width rows indices a := by
  obtain ⟨m, _, e, hrun, hs⟩ := ExecSunflowerCallback.command_eval
    F mask limit width rows indices a
    (ExecSunflowerCallback.fresh_of_invariant F mask limit width rows indices a hi ht)
  have hb : b = e := Eval.final_unique 17 he hrun
  simpa only [hb] using hs

/-- A nonempty witness skips the callback regardless of all other data. -/
theorem callback_saved (a b : Data) (n : ℕ) (h21 : a.stacks 21 ≠ [])
    (he : Eval ExecSunflowerCallback.command n a b) : b.stacks = a.stacks := by
  obtain ⟨m, _, e, hrun, hs⟩ := ExecSunflowerCallback.command_eval [] [] [] [] [] [] a
    (by intro h; exact False.elim (h21 h))
  have hb : b = e := Eval.final_unique 17 he hrun
  rw [hb, hs]
  simp [ExecSunflowerCallback.outputStacks, h21]

/-- In particular, saved core 8, family 13, and witness 21 survive every later
callback and every later odometer step. -/
theorem saved_persistent {shape ranks : List ℕ} {n : ℕ} {a b : Data}
    (h : Visits ports ExecSunflowerCallback.command shape ranks n a b)
    (h21 : a.stacks 21 ≠ []) :
    ∀ i : Fin 32, i ≠ 17 → i ≠ 18 → b.stacks i = a.stacks i := by
  induction h with
  | done => intros; rfl
  | @step tuple a e f nb na nt ranks hf hw hc he hcounter hadv htail ih =>
    have hes : e.stacks = a.stacks := callback_saved a e nb h21 he
    have hnext : (advanceResult ports e tuple).stacks 21 ≠ [] := by
      have hframe := advanceResult_outside ports e tuple 21 (by decide) (by decide)
      rw [← hframe, hes]
      exact h21
    intro i hi17 hi18
    exact (ih hnext i hi17 hi18).trans
      ((advanceResult_outside ports e tuple i hi17 hi18).symm.trans (congrFun hes i))

theorem empty_before_of_empty_after {shape ranks : List ℕ} {n : ℕ} {a b : Data}
    (h : Visits ports ExecSunflowerCallback.command shape ranks n a b)
    (hb : b.stacks 21 = []) : a.stacks 21 = [] := by
  by_contra ha
  exact ha ((saved_persistent h ha 21 (by decide) (by decide)).symm.trans hb)

/-- Extract an actual rank hit with both the runtime invariant and empty
witnesses. Final absence is propagated backwards through the concrete loop. -/
theorem hit_empty (F : Formula) (limit width rows : List Bool) (k r w budget : ℕ)
    (hbudget : BodyBudget F limit width rows k r w budget)
    {ranks : List ℕ} {n : ℕ} {a b : Data}
    (h : Visits ports ExecSunflowerCallback.command (k :: List.replicate r w) ranks n a b)
    (hi : Invariant F limit width rows a) (hs : a.stacks 18 = [])
    (hb : b.stacks 21 = []) {rank : ℕ} (hr : rank ∈ ranks) :
    ∃ (tuple : List (List Bool)) (c e : Data) (nb : ℕ),
      tuple.map List.length = k :: List.replicate r w ∧
      CounterPrograms.value tuple.flatten = rank ∧
      c.stacks 17 = Encoding.encodeList id tuple ∧ Eval ExecSunflowerCallback.command nb c e ∧
      Invariant F limit width rows c ∧ c.stacks 21 = [] ∧ e.stacks 21 = [] := by
  induction h with
  | done => simp at hr
  | @step tuple a e f nb na nt ranks hf hw hc he hcounter hadv htail ih =>
    have hpres := (callback_spec F limit width rows k r w budget hbudget).preserves
      tuple a e nb hw hi hc hs he
    have hnextI : Invariant F limit width rows (advanceResult ports e tuple) :=
      invariant_stable F limit width rows 0 e _ (advanceResult_outside ports e tuple) hpres.1
    have hnextEmpty := empty_before_of_empty_after htail hb
    have he21 : e.stacks 21 = [] :=
      (advanceResult_outside ports e tuple 21 (by decide) (by decide)).trans hnextEmpty
    rcases List.mem_cons.mp hr with hhead | htailRank
    · have ha21 := empty_before_of_empty_after
        (Visits.step hf hw hc he hcounter hadv htail) hb
      exact ⟨tuple, a, e, nb, hw, hhead.symm, hc, he, hi, ha21, he21⟩
    · exact ih hnextI (advanceResult_scratch ports e tuple) hb htailRank

/-- A failed width has no accepted candidate of the enumerated shape. This
uses actual callback hits; it is independent of the old abstract selector. -/
theorem no_candidate_of_empty (F : Formula) (limit width rows : List Bool)
    (k r w budget : ℕ) (hbudget : BodyBudget F limit width rows k r w budget)
    {n : ℕ} {a b : Data}
    (h : Visits ports ExecSunflowerCallback.command (k :: List.replicate r w)
      (List.range' 0 (2 ^ (k + r * w))) n a b)
    (hi : Invariant F limit width rows a) (hs : a.stacks 18 = []) (hb : b.stacks 21 = [])
    (mask : List Bool) (indices : List (List Bool))
    (hm : mask.length = k) (hw : indices.map List.length = List.replicate r w) :
    ExecSunflowerCallback.accepted F mask limit width rows indices = false := by
  let target := mask :: indices
  have ht : target.map List.length = k :: List.replicate r w := by simp [target, hm, hw]
  have hbits : target.flatten.length = k + r * w := by
    have hh := congrArg List.sum ht
    simpa only [List.length_flatten, List.sum_cons, List.sum_replicate, smul_eq_mul] using hh
  have hv : CounterPrograms.value target.flatten < 2 ^ (k + r * w) := by
    simpa only [hbits] using ExecCNFTupleOdometer.value_lt_power_length target.flatten
  have hmem : CounterPrograms.value target.flatten ∈ List.range' 0 (2 ^ (k + r * w)) := by
    simpa only [List.mem_range'_1, Nat.zero_le, zero_add, true_and] using hv
  obtain ⟨tuple, c, e, nb, hshape, hvalue, hc, he, hci, hc21, he21⟩ :=
    hit_empty F limit width rows k r w budget hbudget h hi hs hb hmem
  have htuple : tuple = target := tuple_eq_of_shape_value (hshape.trans ht.symm) hvalue
  subst tuple
  have hout := callback_output F mask limit width rows indices c e nb hci hc he
  have hsave : ExecCNFFirstWitness.save (c.stacks 17) []
      (ExecSunflowerCallback.accepted F mask limit width rows indices) = [] := by
    rw [hout, ExecSunflowerCallback.outputStacks_witness, hc21] at he21
    exact he21
  cases ha : ExecSunflowerCallback.accepted F mask limit width rows indices with
  | false => rfl
  | true =>
    have hempty : c.stacks 17 = [] := by simpa [ExecCNFFirstWitness.save, ha] using hsave
    rw [hc] at hempty
    simp [target, Encoding.encodeList] at hempty

theorem visits_frame (F : Formula) (limit width rows : List Bool) (k r w budget : ℕ)
    (hbudget : BodyBudget F limit width rows k r w budget)
    {ranks : List ℕ} {n : ℕ} {a b : Data}
    (h : Visits ports ExecSunflowerCallback.command (k :: List.replicate r w) ranks n a b)
    (hi : Invariant F limit width rows a) (hs : a.stacks 18 = [])
    (i : Fin 32) (h8 : i ≠ 8) (h13 : i ≠ 13) (h17 : i ≠ 17)
    (h18 : i ≠ 18) (h21 : i ≠ 21) : b.stacks i = a.stacks i := by
  induction h with
  | done => rfl
  | @step tuple a e f nb na nt ranks hf hw hc he hcounter hadv htail ih =>
    have hpres := (callback_spec F limit width rows k r w budget hbudget).preserves
      tuple a e nb hw hi hc hs he
    have hnextI : Invariant F limit width rows (advanceResult ports e tuple) :=
      invariant_stable F limit width rows 0 e _ (advanceResult_outside ports e tuple) hpres.1
    have hcb : e.stacks i = a.stacks i := by
      cases tuple with
      | nil => simp at hw
      | cons mask indices =>
        rw [callback_output F mask limit width rows indices a e nb hi hc he]
        exact ExecSunflowerCallback.outputStacks_frame F mask limit width rows indices a i h8 h13 h21
    exact (ih hnextI (advanceResult_scratch ports e tuple)).trans
      ((advanceResult_outside ports e tuple i h17 h18).symm.trans hcb)

theorem encoded_length_of_shape (tuple : List (List Bool)) (shape : List ℕ)
    (h : tuple.map List.length = shape) :
    (Encoding.encodeList id tuple).length = 2 * shape.sum + 2 * shape.length + 1 := by
  have hn : tuple.length = shape.length := by simpa using congrArg List.length h
  have hb : tuple.flatten.length = shape.sum := by
    simpa only [List.length_flatten] using congrArg List.sum h
  rw [ExecCNFTupleOdometer.encoded_length, hn, hb]

/-- The final overflow step preserves the serialized shape; clearing its
output therefore has the same local length bound as every other iteration. -/
theorem final_encoded_length {shape ranks : List ℕ} {n : ℕ} {a b : Data}
    (h : Visits ports ExecSunflowerCallback.command shape ranks n a b)
    (ha : (a.stacks 17).length = 2 * shape.sum + 2 * shape.length + 1) :
    (b.stacks 17).length = 2 * shape.sum + 2 * shape.length + 1 := by
  induction h with
  | done => exact ha
  | @step tuple d e f nb na nt ranks hf hw hc he hcounter hadv htail ih =>
    apply ih
    change ((advanceResult ports e tuple).stacks ports.counter).length = _
    rw [advanceResult_counter, bumpWords_encoded_length]
    exact encoded_length_of_shape tuple shape hw

abbrev command (k : ℕ) : Cmd 32 32 :=
  .seq (ExecCNFTupleInitialize.command k)
    (.seq (enumerate ports ExecSunflowerCallback.command) (ExecCNFTupleSplit.clear 17))

def bound (k r w budget initBudget : ℕ) : ℕ :=
  let L := 2 * (k + r * w) + 2 * (r + 1) + 1
  initBudget + 2 ^ (k + r * w) * (budget + 7 * L + 5) + 2 * L + 5

def program (k : ℕ) := compiled (command k) 16 21

/-- Concrete initialization, exhaustive callback loop, and tuple cleanup.
The log consists of actual callback executions, including the terminal rank. -/
theorem command_eval (F : Formula) (limit width : List Bool) (k budget : ℕ) (d : Data)
    (hi : Invariant F limit width (d.stacks 15) d)
    (hready : ExecCNFTupleInitialize.Ready d) (hs : d.stacks 18 = [])
    (hb : BodyBudget F limit width (d.stacks 15) k
      (CounterPrograms.value (d.stacks 15)) (CounterPrograms.value (d.stacks 20)) budget) :
    ∃ (n : ℕ) (a e f : Data), Eval (command k) n d f ∧
      n ≤ bound k (CounterPrograms.value (d.stacks 15))
        (CounterPrograms.value (d.stacks 20)) budget
        (ExecCNFTupleInitialize.bound k (d.stacks 15) (d.stacks 20)) ∧
      Invariant F limit width (d.stacks 15) f ∧ f.stacks 17 = [] ∧ f.stacks 18 = [] ∧
      (∀ i : Fin 32, i ≠ 8 → i ≠ 13 → i ≠ 17 → i ≠ 21 → f.stacks i = d.stacks i) ∧
      a.stacks 21 = d.stacks 21 ∧ f.stacks = StackRoutines.clearStacks 17 e.stacks ∧
      f.stacks 21 = e.stacks 21 ∧
      Invariant F limit width (d.stacks 15) a ∧ a.stacks 18 = [] ∧
      ∃ loopSteps, Visits ports ExecSunflowerCallback.command
        (k :: List.replicate (CounterPrograms.value (d.stacks 15))
          (CounterPrograms.value (d.stacks 20)))
        (List.range' 0 (2 ^ (k + CounterPrograms.value (d.stacks 15) *
          CounterPrograms.value (d.stacks 20)))) loopSteps a e := by
  let tuple := ExecCNFTupleInitialize.words k (d.stacks 15) (d.stacks 20)
  let shape := k :: List.replicate (CounterPrograms.value (d.stacks 15))
    (CounterPrograms.value (d.stacks 20))
  let L := 2 * shape.sum + 2 * shape.length + 1
  obtain ⟨ni, a, hinit, hni, ha17, haf⟩ := ExecCNFTupleInitialize.command_eval k d hready
  have has : a.stacks 18 = [] := (haf 18 (by decide)).trans hs
  have hai : Invariant F limit width (d.stacks 15) a :=
    invariant_stable F limit width _ 0 d a (fun i h17 _ => (haf i h17).symm) hi
  have hshape : tuple.map List.length = shape :=
    ExecCNFTupleInitialize.words_shape k (d.stacks 15) (d.stacks 20)
  have hbits : tuple.flatten.length = shape.sum := by
    simpa only [List.length_flatten] using congrArg List.sum hshape
  have hlen : (Encoding.encodeList id tuple).length = L :=
    encoded_length_of_shape tuple shape hshape
  obtain ⟨nl, e, hloop, hlog, hei, heflag, hes, hnl⟩ := enumerate_correct
    ports ExecSunflowerCallback.command shape (Invariant F limit width (d.stacks 15)) budget
    (invariant_stable F limit width _) (callback_spec F limit width _ k _ _ budget hb)
    tuple a hshape hai ha17 has (ExecCNFTupleInitialize.words_value k _ _)
  have helen : (e.stacks 17).length = L :=
    final_encoded_length hlog (by change (a.stacks 17).length = L; rw [ha17]; exact hlen)
  let f := ExecCNFTupleSplit.cleared 17 e
  have hfi : Invariant F limit width (d.stacks 15) f :=
    invariant_stable F limit width _ 0 e f
      (fun i h17 _ => (ExecCNFTupleSplit.cleared_stack_frame 17 e i h17).symm) hei
  refine ⟨ni + ((1 + nl) + (2 * (e.stacks 17).length + 3)), startResult ports a, e, f,
    Eval.seq hinit (Eval.seq hloop (ExecCNFTupleSplit.clear_eval 17 e)), ?_, hfi, ?_, ?_, ?_, ?_, rfl, ?_,
    ?_, ?_, nl, ?_⟩
  · rw [helen]
    rw [hbits, hlen] at hnl
    have hsum : shape.sum = k + CounterPrograms.value (d.stacks 15) *
        CounterPrograms.value (d.stacks 20) := by simp [shape]
    have hsize : shape.length = CounterPrograms.value (d.stacks 15) + 1 := by simp [shape]
    change _ ≤ _
    simp only [bound]
    dsimp [L] at hnl ⊢
    rw [hsum, hsize] at hnl ⊢
    omega
  · simp [f, ExecCNFTupleSplit.cleared, StackRoutines.clearStacks]
  · exact (ExecCNFTupleSplit.cleared_stack_frame 17 e 18 (by decide)).trans hes
  · intro i hi8 hi13 hi17 hi21
    rw [ExecCNFTupleSplit.cleared_stack_frame 17 e i hi17]
    by_cases hi18 : i = 18
    · subst i
      exact hes.trans hs.symm
    exact (visits_frame F limit width _ k _ _ budget hb hlog hai has i
      hi8 hi13 hi17 hi18 hi21).trans (haf i hi17)
  · exact haf 21 (by decide)
  · exact ExecCNFTupleSplit.cleared_stack_frame 17 e 21 (by decide)
  · exact hai
  · exact has
  · rw [hbits] at hlog
    simpa only [shape, List.sum_cons, List.sum_replicate, smul_eq_mul] using hlog

end SubexponentialSAT.ExecCNFWidthSearch

end OAI.Algorithms
