import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedTupleStep
import OAI.Algorithms.SubexponentialSAT.SubexpNodeCost
import OAI.Algorithms.SubexponentialSAT.SubexpEnumerationPayload

namespace OAI.Algorithms

/-!
# Fixed-depth ordered tuple generation

The programs at depths two and four have fixed finite instruction tables.
Each Cartesian expansion is followed by the actual record reversal routine,
so the output order agrees exactly with QuarticSearch.vectors.
-/

namespace SubexponentialSAT.SubexpOrderedTupleProgram

open BitProgram StructuredCalls Subexp.TupleProgram SubexpOrderedTupleData

def repeatSteps : ℕ → Cmd 10 9
  | 0 => .base .skip
  | n + 1 => .seq SubexpOrderedTupleStep.step (repeatSteps n)

def repeatCost (alphabet : List (List Bool)) : ℕ → List (List Bool) → ℕ
  | 0, _ => 0
  | n + 1, rows => SubexpOrderedTupleStep.stepCost rows alphabet +
      repeatCost alphabet n (orderedCartesian rows alphabet)

theorem repeat_eval (n : ℕ) (alphabet rows : List (List Bool))
    (depth : List Bool) (guard : Bool) (a : State 10 9)
    (ha : Ready alphabet rows depth guard a) :
    ∃ k next, k ≤ repeatCost alphabet n rows ∧
      Ready alphabet (orderedRows alphabet n rows) depth guard next ∧
      Eval (repeatSteps n) k a next := by
  induction n generalizing rows a with
  | zero => exact ⟨0, a, by simp [repeatCost], ha, Eval.base (StructuredProgram.Eval.skip a)⟩
  | succ n ih =>
      obtain ⟨k, b, hk, hb, he⟩ := SubexpOrderedTupleStep.step_eval alphabet rows depth guard a ha
      obtain ⟨m, c, hm, hc, hf⟩ := ih (orderedCartesian rows alphabet) b hb
      exact ⟨k + m, c, Nat.add_le_add hk hm, hc, he.seq hf⟩

abbrev cmd (n : ℕ) : Cmd 10 9 := .seq initCmd (repeatSteps n)
def program (n : ℕ) := StructuredCalls.compiled (cmd n) 1 0
def cost (alphabet : List (List Bool)) (n : ℕ) : ℕ := repeatCost alphabet n [[]] + 9

theorem program_runsIn (n : ℕ) (alphabet : List (List Bool))
    (depth : List Bool) (guard : Bool) (a : State 10 9)
    (ha : outerInvariant alphabet depth guard a)
    (h0 : a.stacks 0 = []) (h2 : a.stacks 2 = []) (h5 : a.stacks 5 = []) :
    ∃ next, Ready alphabet (orderedRows alphabet n [[]]) depth guard next ∧
      RunsIn (program n) (cost alphabet n)
        (a.withPC (some (program n).entry)) (next.withPC none) := by
  obtain ⟨b, hb, hi⟩ := initCmd_eval alphabet depth guard a ha h0 h2 h5
  obtain ⟨k, next, hk, hnext, he⟩ := repeat_eval n alphabet [[]] depth guard b hb
  exact ⟨next, hnext, 8 + k + 1, by unfold cost; omega,
    compiled_halt_trace (hi.seq he) 1 0⟩

def inputState (alphabet : List (List Bool)) : State 10 9 :=
  ⟨fun _ => false, fun i => if i = 1 then ProgramEncoding.encodeRecords alphabet else []⟩

theorem initial_runsIn (n : ℕ) (alphabet : List (List Bool)) :
    ∃ next : State 10 9,
      next.stacks 0 = ProgramEncoding.encodeRecords
        ((QuarticSearch.vectors alphabet n).map SubexpTupleRefinement.tuplePayload) ∧
      RunsIn (program n) (cost alphabet n)
        (initial (program n) (ProgramEncoding.encodeRecords alphabet)) (next.withPC none) := by
  have ha : outerInvariant alphabet [] false (inputState alphabet) := by
    simp [outerInvariant, inputState]
  obtain ⟨next, hnext, hr⟩ := program_runsIn n alphabet [] false (inputState alphabet)
    ha (by simp [inputState]) (by simp [inputState]) (by simp [inputState])
  exact ⟨next, by simpa only [orderedRows_empty] using hnext.2.1, hr⟩

/-- Exact source-vector order, rather than only a permutation of candidates. -/
theorem selected_runsIn (n p : ℕ) [Fact p.Prime] :
    ∃ next : State 10 9,
      next.stacks 0 = ProgramEncoding.encodeRecords
        ((QuarticSearch.vectors (QuarticSearch.elements p) n).map
          (SubexpTupleRefinement.encodeTuple (SubexpEnumerationPayload.scalarCode p))) ∧
      RunsIn (program n)
        (cost ((QuarticSearch.elements p).map (SubexpEnumerationPayload.scalarCode p).block) n)
        (initial (program n) (ProgramEncoding.encodeRecords
          ((QuarticSearch.elements p).map (SubexpEnumerationPayload.scalarCode p).block)))
        (next.withPC none) := by
  obtain ⟨next, hnext, hr⟩ := initial_runsIn n
    ((QuarticSearch.elements p).map (SubexpEnumerationPayload.scalarCode p).block)
  refine ⟨next, ?_, hr⟩
  rw [← orderedRows_empty, orderedRows_encoded] at hnext
  exact hnext

def pairs := program 2
def quartics := program 4

theorem payloadSize_orderedCartesian (rows alphabet : List (List Bool)) :
    SubexpNodeCost.payloadSize (orderedCartesian rows alphabet) =
      alphabet.length * SubexpNodeCost.payloadSize rows +
        rows.length * SubexpNodeCost.payloadSize alphabet := by
  rw [orderedCartesian_eq_reverse, SubexpNodeCost.payloadSize_reverse,
    SubexpNodeCost.payloadSize_cartesian]

theorem stepCost_eq (rows alphabet : List (List Bool)) :
    SubexpOrderedTupleStep.stepCost rows alphabet =
      17 + (32 * alphabet.length + 8) * SubexpNodeCost.payloadSize rows +
        (45 * SubexpNodeCost.payloadSize alphabet + 56 * alphabet.length + 25) * rows.length := by
  rw [SubexpOrderedTupleStep.stepCost, SubexpNodeCost.expansionCost_eq,
    ProgramEncoding.encodeRecords_length]
  change _ + 10 * (2 * SubexpNodeCost.payloadSize (cartesianOutput rows alphabet) +
    2 * (cartesianOutput rows alphabet).length + 1) + 4 = _
  rw [SubexpNodeCost.payloadSize_cartesian, cartesianOutput_length]
  ring

theorem cost_four (alphabet : List (List Bool)) :
    cost alphabet 4 =
      SubexpNodeCost.payloadSize alphabet *
        (141 * alphabet.length^3 + 133 * alphabet.length^2 + 93 * alphabet.length + 53) +
      (56 * alphabet.length^4 + 81 * alphabet.length^3 + 81 * alphabet.length^2 +
        81 * alphabet.length + 102) := by
  simp only [cost, repeatCost, stepCost_eq, payloadSize_orderedCartesian,
    orderedCartesian_length, SubexpNodeCost.payloadSize_cons, SubexpNodeCost.payloadSize_nil,
    List.length_cons, List.length_nil]
  ring

theorem cost_four_le (alphabet : List (List Bool)) (width : ℕ)
    (h : ∀ word ∈ alphabet, word.length ≤ width) :
    cost alphabet 4 ≤ 1000 * (alphabet.length + 1)^4 * (width + 1) := by
  rw [cost_four]
  have hs := SubexpNodeCost.payloadSize_le alphabet width h
  set q := alphabet.length
  calc
    _ ≤ (q * width) * (141*q^3 + 133*q^2 + 93*q + 53) +
        (56*q^4 + 81*q^3 + 81*q^2 + 81*q + 102) :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ hs) _
    _ ≤ _ + (859*width*q^4 + 3867*width*q^3 + 5907*width*q^2 + 3947*width*q +
        1000*width + 944*q^4 + 3919*q^3 + 5919*q^2 + 3919*q + 898) :=
      Nat.le_add_right _ _
    _ = _ := by ring

theorem cost_two_le (alphabet : List (List Bool)) (width : ℕ)
    (h : ∀ word ∈ alphabet, word.length ≤ width) :
    cost alphabet 2 ≤ 1000 * (alphabet.length + 1)^4 * (width + 1) := by
  apply le_trans _ (cost_four_le alphabet width h)
  unfold cost
  simp only [repeatCost]
  omega

theorem selected_primitive_runsIn (n p : ℕ) [Fact p.Prime] :
    ∃ next : State 10 9,
      next.stacks 0 = ProgramEncoding.encodeRecords
        ((QuarticSearch.vectors (QuarticSearch.elements p) n).map
          (SubexpTupleRefinement.encodeTuple (SubexpEnumerationPayload.scalarCode p))) ∧
      Computation.RunsIn (primitive (program n)).step
        (primitiveOverhead (program n) *
          cost ((QuarticSearch.elements p).map (SubexpEnumerationPayload.scalarCode p).block) n)
        (primitiveCfg (program n) (initial (program n) (ProgramEncoding.encodeRecords
          ((QuarticSearch.elements p).map (SubexpEnumerationPayload.scalarCode p).block))))
        (primitiveCfg (program n) (next.withPC none)) := by
  obtain ⟨next, hout, hr⟩ := selected_runsIn n p
  exact ⟨next, hout, primitive_execution (program n) hr⟩

end SubexponentialSAT.SubexpOrderedTupleProgram

end OAI.Algorithms
