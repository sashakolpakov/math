import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedSetupBounds
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram

namespace OAI.Algorithms

/-!
# Fixed physical storage for prepared-ring staging

These generic rules execute a supplied finite 16-register/34-stack table
inside a fixed 51-stack staging interface. The concrete two-ring module
instantiates the table with the proved prepared-ring setup program.
-/

namespace SubexponentialSAT.SubexpPreparedRingStaging

open BitProgram StructuredCalls SubexpSetupStorage
open SubexpPreparedSetupCalls (StackBound)

abbrev Data := StructuredProgram.State 16 51
abbrev Command := Cmd 16 51

def calleePort (i : Fin 34) : Fin 51 := i.castAdd 17
def calleePorts : List (Fin 51) := List.ofFn calleePort
def scratchPorts : List (Fin 51) := List.ofFn (fun i : Fin 36 => i.castAdd 15)
def copyTemporary : Fin 51 := 34
def literalPort : Fin 51 := 35
def inputPort (i : Fin 3) : Fin 51 := ⟨36 + i.val, by omega⟩
def precisionPort (source : Bool) : Fin 51 := if source then literalPort else 37
def destination (source : Bool) (i : Fin 6) : Fin 51 :=
  ⟨(if source then 45 else 39) + i.val, by cases source <;> simp_all <;> omega⟩
def calleeOutput (i : Fin 6) : Fin 34 := ⟨27 + i.val, by omega⟩

def inputCopies (source : Bool) : List (Fin 51 × Fin 51) :=
  [(36, 24), (precisionPort source, 25), (38, 26)]
def outputCopies (source : Bool) : List (Fin 51 × Fin 51) :=
  List.ofFn (fun i : Fin 6 => (calleePort (calleeOutput i), destination source i))

theorem calleePort_injective : Function.Injective calleePort := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 51 => k.val) h)

theorem mem_calleePorts (i : Fin 51) : i ∈ calleePorts ↔ i.val < 34 := by
  simp only [calleePorts, List.mem_ofFn]
  constructor
  · rintro ⟨j, rfl⟩
    exact j.isLt
  · intro hi
    exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩

theorem mem_scratchPorts (i : Fin 51) : i ∈ scratchPorts ↔ i.val < 36 := by
  simp only [scratchPorts, List.mem_ofFn]
  constructor
  · rintro ⟨j, rfl⟩
    exact j.isLt
  · intro hi
    exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩

theorem inputCopies_good (source : Bool) :
    ∀ q ∈ inputCopies source,
      q.1 ≠ q.2 ∧ q.1 ≠ copyTemporary ∧ copyTemporary ≠ q.2 := by
  intro q hq
  simp only [inputCopies, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl <;> cases source <;> decide

theorem inputCopies_separated (source : Bool) :
    ∀ q ∈ inputCopies source, ∀ z ∈ inputCopies source, q.1 ≠ z.2 := by
  intro q hq z hz
  simp only [inputCopies, List.mem_cons, List.not_mem_nil, or_false] at hq hz
  rcases hq with rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl <;> cases source <;> decide

theorem inputCopies_nodup (source : Bool) : ((inputCopies source).map Prod.snd).Nodup := by
  cases source <;> decide

theorem inputCopies_in_ports (source : Bool) :
    ∀ q ∈ inputCopies source, q.2 ∈ calleePorts := by
  intro q hq
  rw [mem_calleePorts]
  cases source <;> simp [inputCopies, precisionPort] at hq <;>
    rcases hq with rfl | rfl | rfl <;> decide

theorem outputCopies_good (source : Bool) :
    ∀ q ∈ outputCopies source,
      q.1 ≠ q.2 ∧ q.1 ≠ copyTemporary ∧ copyTemporary ≠ q.2 := by
  intro q hq
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
  cases source <;> fin_cases i <;> decide

theorem outputCopies_separated (source : Bool) :
    ∀ q ∈ outputCopies source, ∀ z ∈ outputCopies source, q.1 ≠ z.2 := by
  intro q hq z hz
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
  cases source <;> fin_cases i <;> fin_cases j <;> decide

theorem outputCopies_nodup (source : Bool) : ((outputCopies source).map Prod.snd).Nodup := by
  cases source <;> decide

def prepared (source : Bool) (a : Data) : Data :=
  RegisterResetProgram.zeroed (prepareState copyTemporary calleePorts (inputCopies source) a)

noncomputable def middle (source : Bool) (a : Data)
    (out : SubexpPreparedSetupCalls.Data) : Data :=
  embedState id calleePort (prepared source a) out

noncomputable def returned (source : Bool) (a : Data)
    (out : SubexpPreparedSetupCalls.Data) : Data :=
  finishState calleePorts (outputCopies source) (middle source a out)

abbrev stageWith {l : ℕ} (setup : Program 16 34 l) (source : Bool) : Command :=
  .seq (prepare copyTemporary calleePorts (inputCopies source))
    (.seq RegisterResetProgram.all
      (.seq (invoke setup id calleePort)
        (finish copyTemporary calleePorts (outputCopies source))))

noncomputable def stageCost (source : Bool) (a : Data)
    (out : SubexpPreparedSetupCalls.Data) (t : ℕ) : ℕ :=
  prepareCost copyTemporary calleePorts (inputCopies source) a +
    (16 + (t + finishCost calleePorts (outputCopies source) (middle source a out)))

theorem prepared_frame (source : Bool) (a : Data) (i : Fin 51) (hi : 34 < i.val) :
    (prepared source a).stacks i = a.stacks i := by
  change (prepareState copyTemporary calleePorts (inputCopies source) a).stacks i = a.stacks i
  apply prepare_frame
  · intro h
    have := congrArg (fun j : Fin 51 => j.val) h
    change i.val = 34 at this
    omega
  · rw [mem_calleePorts]
    omega
  · intro q hq h
    have hp := inputCopies_in_ports source q hq
    rw [mem_calleePorts] at hp
    have := congrArg (fun j : Fin 51 => j.val) h
    omega

theorem prepared_word (source : Bool) (a : Data) (q : Fin 51 × Fin 51)
    (hq : q ∈ inputCopies source) :
    (prepared source a).stacks q.2 = a.stacks q.1 := by
  have hz : ∀ z ∈ inputCopies source,
      (beforeCopies copyTemporary calleePorts a).stacks z.2 = [] := by
    intro z hz
    simp only [beforeCopies, resetMany_stacks, clearMany_stacks,
      ite_eq_left (inputCopies_in_ports source z hz)]
  change (copyManyState (inputCopies source)
    (beforeCopies copyTemporary calleePorts a)).stacks q.2 = _
  rw [copyMany_value _ _ (inputCopies_nodup source) hz (inputCopies_separated source) q hq]
  have hlow : 34 < q.1.val := by
    cases source <;> simp [inputCopies, precisionPort, literalPort] at hq <;>
      rcases hq with rfl | rfl | rfl <;> decide
  have hn : q.1 ∉ calleePorts := by rw [mem_calleePorts]; omega
  have ht : q.1 ≠ copyTemporary := by
    intro h
    have := congrArg (fun j : Fin 51 => j.val) h
    change q.1.val = 34 at this
    omega
  simp only [beforeCopies, resetMany_stacks, clearMany_stacks, ite_eq_right hn]
  simp [ht]

theorem prepared_empty (source : Bool) (a : Data) (j : Fin 34)
    (hj : ∀ q ∈ inputCopies source, calleePort j ≠ q.2) :
    (prepared source a).stacks (calleePort j) = [] := by
  change (copyManyState (inputCopies source)
    (beforeCopies copyTemporary calleePorts a)).stacks (calleePort j) = []
  rw [copyMany_frame _ _ _ hj]
  simp only [beforeCopies, resetMany_stacks, clearMany_stacks,
    ite_eq_left ((mem_calleePorts (calleePort j)).mpr j.isLt)]

def inputState (prime precision coeff : List Bool) : SubexpPreparedSetupCalls.Data :=
  ⟨fun _ => false,
    Function.update
      (Function.update (Function.update (fun _ => []) (SubexpPreparedSetupCalls.cache 0) prime)
        (SubexpPreparedSetupCalls.cache 1) precision)
      (SubexpPreparedSetupCalls.cache 2) coeff⟩

theorem prepared_eq_words (source : Bool) (a : Data) :
    project id calleePort (prepared source a) =
      inputState (a.stacks 36) (a.stacks (precisionPort source)) (a.stacks 38) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext j
    by_cases h24 : j = 24
    · subst j
      simpa [inputState, SubexpPreparedSetupCalls.cache,
        Function.update_apply,
        show calleePort (24 : Fin 34) = (24 : Fin 51) from Fin.ext rfl] using
          prepared_word source a (36, 24) (by simp [inputCopies])
    by_cases h25 : j = 25
    · subst j
      simpa [inputState, SubexpPreparedSetupCalls.cache,
        Function.update_apply,
        show calleePort (25 : Fin 34) = (25 : Fin 51) from Fin.ext rfl] using
          prepared_word source a (precisionPort source, 25) (by simp [inputCopies])
    by_cases h26 : j = 26
    · subst j
      simpa [inputState, SubexpPreparedSetupCalls.cache,
        Function.update_apply,
        show calleePort (26 : Fin 34) = (26 : Fin 51) from Fin.ext rfl] using
          prepared_word source a (38, 26) (by simp [inputCopies])
    have he := prepared_empty source a j (by
      intro q hq
      simp only [inputCopies, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact fun h => h24 (Fin.ext (congrArg (fun k : Fin 51 => k.val) h))
      · exact fun h => h25 (Fin.ext (congrArg (fun k : Fin 51 => k.val) h))
      · exact fun h => h26 (Fin.ext (congrArg (fun k : Fin 51 => k.val) h)))
    simpa [inputState, SubexpPreparedSetupCalls.cache,
      Function.update_apply, h24, h25, h26] using he

theorem stageWith_eval {l : ℕ} (setup : Program 16 34 l) (source : Bool) (a : Data) (out : SubexpPreparedSetupCalls.Data)
    {t : ℕ}
    (ht : Trace setup t
      ((project id calleePort (prepared source a)).withPC
        (some setup.entry)) (out.withPC none)) :
    Eval (stageWith setup source) (stageCost source a out t) a (returned source a out) := by
  have htmp : (middle source a out).stacks copyTemporary = [] := by
    unfold middle
    rw [embedState_stack_frame]
    · exact prepare_temporary copyTemporary calleePorts (inputCopies source) a
        (inputCopies_good source)
    · rintro ⟨j, hj⟩
      have := congrArg (fun i : Fin 51 => i.val) hj
      change j.val = 34 at this
      omega
  exact .seq (prepare_eval copyTemporary calleePorts (inputCopies source) a
      (inputCopies_good source))
    (.seq (RegisterResetProgram.all_eval _)
      (.seq (invoke_eval setup id calleePort
        Function.injective_id calleePort_injective (prepared source a) out ht)
        (finish_eval copyTemporary calleePorts (outputCopies source) (middle source a out)
          (outputCopies_good source) htmp)))

theorem returned_word (source : Bool) (a : Data) (out : SubexpPreparedSetupCalls.Data)
    (i : Fin 6) : (returned source a out).stacks (destination source i) =
      out.stacks (calleeOutput i) := by
  have hm : (calleePort (calleeOutput i), destination source i) ∈ outputCopies source :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  have hn : destination source i ∉ calleePorts := by
    rw [mem_calleePorts]
    cases source <;> simp [destination] <;> omega
  exact (finish_value calleePorts (outputCopies source) (middle source a out)
    (outputCopies_nodup source) (outputCopies_separated source) _ hm hn).trans
      (embedState_stack id calleePort (prepared source a) out calleePort_injective _)

theorem returned_frame (source : Bool) (a : Data) (out : SubexpPreparedSetupCalls.Data)
    (i : Fin 51) (hi : 34 < i.val) (hd : ∀ j, i ≠ destination source j) :
    (returned source a out).stacks i = a.stacks i := by
  have hn : i ∉ calleePorts := by rw [mem_calleePorts]; omega
  have ho : ∀ q ∈ outputCopies source, i ≠ q.2 := by
    intro q hq
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    exact hd j
  exact (finish_frame calleePorts (outputCopies source) _ i hn ho).trans
    ((embedState_stack_frame id calleePort _ out i (by
      rintro ⟨j, hj⟩
      exact hn (List.mem_ofFn.mpr ⟨j, hj⟩))).trans (prepared_frame source a i hi))

private theorem prepared_bound (source : Bool) (a : Data) {W : ℕ}
    (ha : StackBound a W) : StackBound (prepared source a) W := by
  apply SubexpPreparedSetupCalls.copyMany_bound _ _
    (SubexpPreparedSetupCalls.beforeCopies_bound copyTemporary calleePorts a ha)
    (inputCopies_nodup source) _ (inputCopies_separated source)
  intro q hq
  simp only [beforeCopies, resetMany_stacks, clearMany_stacks,
    ite_eq_left (inputCopies_in_ports source q hq)]

private theorem middle_bound (source : Bool) (a : Data)
    (out : SubexpPreparedSetupCalls.Data) {W : ℕ}
    (ha : StackBound a W) (hout : StackBound out W) : StackBound (middle source a out) W := by
  intro i
  by_cases hi : ∃ j, calleePort j = i
  · obtain ⟨j, rfl⟩ := hi
    unfold middle
    rw [embedState_stack _ _ _ _ calleePort_injective]
    exact hout j
  · unfold middle
    rw [embedState_stack_frame _ _ _ _ _ hi]
    exact prepared_bound source a ha i

private theorem finish_copies_bound (source : Bool) (a : Data) {W : ℕ}
    (ha : StackBound a W) : StackBound
      (copyManyState (outputCopies source)
        (clearManyState ((outputCopies source).map Prod.snd) a)) W := by
  apply SubexpPreparedSetupCalls.copyMany_bound _ _
    (SubexpPreparedSetupCalls.clearMany_bound _ a ha)
    (outputCopies_nodup source) _ (outputCopies_separated source)
  intro q hq
  rw [clearMany_stacks, ite_eq_left (List.mem_map.mpr ⟨q, hq, rfl⟩)]

theorem returned_bound (source : Bool) (a : Data)
    (out : SubexpPreparedSetupCalls.Data) {W : ℕ}
    (ha : StackBound a W) (hout : StackBound out W) : StackBound (returned source a out) W := by
  intro i
  change ((resetManyState workRegisters (clearManyState calleePorts _)).stacks i).length ≤ W
  rw [resetMany_stacks]
  exact SubexpPreparedSetupCalls.clearMany_bound calleePorts _
    (finish_copies_bound source _ (middle_bound source a out ha hout)) i

theorem stageCost_le (source : Bool) (a : Data) (out : SubexpPreparedSetupCalls.Data)
    (t W : ℕ) (ha : StackBound a W) (hout : StackBound out W) :
    stageCost source a out t ≤ t + 400 * (W + 1) := by
  have h1 := SubexpPreparedSetupCalls.clearManyCost_le [copyTemporary] a ha
  have h2 := SubexpPreparedSetupCalls.clearManyCost_le calleePorts
    (clearManyState [copyTemporary] a) (SubexpPreparedSetupCalls.clearMany_bound _ _ ha)
  have h3 := SubexpPreparedSetupCalls.copyManyCost_le (inputCopies source)
    (beforeCopies copyTemporary calleePorts a)
    (fun q _ => SubexpPreparedSetupCalls.beforeCopies_bound copyTemporary calleePorts a ha q.1)
    (inputCopies_separated source)
  have hm := middle_bound source a out ha hout
  have h4 := SubexpPreparedSetupCalls.clearManyCost_le ((outputCopies source).map Prod.snd)
    (middle source a out) hm
  have h5 := SubexpPreparedSetupCalls.copyManyCost_le (outputCopies source)
    (clearManyState ((outputCopies source).map Prod.snd) (middle source a out))
    (fun q _ => SubexpPreparedSetupCalls.clearMany_bound _ _ hm q.1)
    (outputCopies_separated source)
  have h6 := SubexpPreparedSetupCalls.clearManyCost_le calleePorts _
    (finish_copies_bound source _ hm)
  simp only [calleePorts, outputCopies, inputCopies, List.length_ofFn,
    List.length_map, List.length_cons, List.length_nil] at h1 h2 h3 h4 h5 h6
  unfold stageCost prepareCost finishCost
  simp only [calleePorts, outputCopies, inputCopies]
  omega

def literalCommand : Command :=
  .seq (clearCmd literalPort)
    (.seq (.base (.atom (.set 0 true))) (.base (.atom (.push literalPort 0))))

def literalState (a : Data) : Data :=
  ⟨Function.update (clearState literalPort a).regs 0 true,
    Function.update a.stacks literalPort [true]⟩

theorem literal_eval (a : Data) :
    Eval literalCommand (2 * (a.stacks literalPort).length + 5) a (literalState a) := by
  have h := Eval.seq (clear_eval literalPort a)
    (Eval.seq (Eval.base (StructuredProgram.Eval.atom (.set 0 true) _))
      (Eval.base (StructuredProgram.Eval.atom (.push literalPort 0) _)))
  simpa [literalCommand, literalState, clearState, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr, Function.update_idem, Nat.add_assoc] using h

theorem literal_frame (a : Data) (i : Fin 51) (hi : i ≠ literalPort) :
    (literalState a).stacks i = a.stacks i := by simp [literalState, hi]

theorem literal_bound (a : Data) {W : ℕ} (ha : StackBound a W) (hW : 1 ≤ W) :
    StackBound (literalState a) W := by
  intro i
  by_cases hi : i = literalPort
  · subst i
    simpa [literalState] using hW
  · rw [literal_frame a i hi]
    exact ha i

def cleanup : Command := .seq (clearMany scratchPorts) RegisterResetProgram.all
def cleaned (a : Data) : Data := RegisterResetProgram.zeroed (clearManyState scratchPorts a)

theorem cleanup_eval (a : Data) :
    Eval cleanup (clearManyCost scratchPorts a + 16) a (cleaned a) :=
  .seq (clearMany_eval scratchPorts a) (RegisterResetProgram.all_eval _)

theorem cleaned_frame (a : Data) (i : Fin 51) (hi : 36 ≤ i.val) :
    (cleaned a).stacks i = a.stacks i := by
  change (clearManyState scratchPorts a).stacks i = _
  rw [clearMany_stacks, ite_eq_right]
  rw [mem_scratchPorts]
  omega

end SubexponentialSAT.SubexpPreparedRingStaging

end OAI.Algorithms
