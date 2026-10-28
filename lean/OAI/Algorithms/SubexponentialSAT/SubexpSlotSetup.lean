import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSlotProgram
import OAI.Algorithms.SubexponentialSAT.SubexpExponentSourceProgram

namespace OAI.Algorithms

/-! From unary dimension and key width to the actual framed retained-key
master.  The generated exponent stream is consumed by the fixed slot loop;
no precomputed exponent or key list is an input. -/

namespace SubexponentialSAT.SubexpSlotSetup

open BitProgram StructuredCalls
open scoped BigOperators

abbrev Data := StructuredProgram.State 16 128
abbrev Code := StructuredCalls.Cmd 16 128

def registers : Fin 3 → Fin 16 := Fin.castAdd 13
def ports (i : Fin 24) : Fin 128 :=
  if i = 14 then 14 else if i = 20 then 110 else if i = 21 then 111 else Fin.castAdd 104 i

theorem registers_injective : Function.Injective registers := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 16 => i.val) h)

theorem ports_injective : Function.Injective ports := by decide

def restrict (d : Data) : SubexpSlotProgram.Data :=
  ⟨fun i => d.regs (registers i), fun i => d.stacks (ports i)⟩

theorem embed_restrict (d : Data) : embedState registers ports d (restrict d) = d := by
  apply embedState_eq_of_ports _ _ _ _ _ registers_injective ports_injective <;> intros <;> rfl

def slotCall : Code := .call (ProgramLinking.liftProgram SubexpSlotProgram.program registers ports)

def output (D : ℕ) : List Bool :=
  Encoding.encodeList id ((SubexpSlotProgram.slots D).map SubexpSymbolicCost.fixedKey).reverse

theorem slotCall_eval (d : Data) (D : ℕ)
    (hc : SubexpSlotProgram.Context (restrict d) D (SubexpSymbolicCost.indexBits D))
    (hreg : ∀ i : Fin 3, d.regs (registers i) = false)
    (h0 : d.stacks 0 = []) (h111 : d.stacks 111 = [])
    (h110 : d.stacks 110 = Encoding.encodeList id (SubexpSlotProgram.momentRecords D))
    (h14 : d.stacks 14 = [false]) :
    ∃ n e, n ≤ 4 + RecordPrograms.budget
        (SubexpSlotProgram.callbackCost D (SubexpSymbolicCost.indexBits D))
        (SubexpSlotProgram.momentRecords D) ∧ Eval slotCall n d e ∧
      e.stacks = Function.update (Function.update d.stacks 110 []) 14 (output D) := by
  have hinv : SubexpSlotProgram.Invariant (restrict d) (restrict d) := by
    constructor
    · exact fun _ _ _ _ _ => rfl
    · exact h0
  obtain ⟨inner, ⟨n, hn, ht⟩, hi, hout⟩ :=
    SubexpSlotProgram.moments_program_runs (restrict d) D hc (restrict d) hinv h14
  have hstart : RecordPrograms.state SubexpSlotProgram.ports (restrict d)
      false false false (Encoding.encodeList id (SubexpSlotProgram.momentRecords D)) [] = restrict d := by
    apply RecordPrograms.state_eq_self
    · exact hreg 0
    · exact hreg 1
    · exact hreg 2
    · exact h110
    · exact h111
  rw [hstart] at ht
  let finalData := RecordPrograms.state SubexpSlotProgram.ports inner false true false [] []
  have hs : finalData.stacks =
      Function.update (Function.update (restrict d).stacks 20 []) 14 (output D) := by
    funext i
    by_cases h20 : i = 20
    · subst i; simp [finalData, RecordPrograms.state, SubexpSlotProgram.ports]
    · by_cases h21 : i = 21
      · subst i
        simp [finalData, RecordPrograms.state, SubexpSlotProgram.ports, restrict, ports, h111]
      · by_cases h14 : i = 14
        · subst i
          simpa [finalData, RecordPrograms.state, SubexpSlotProgram.ports, output] using hout
        · by_cases hx : i = 0
          · subst i
            simp [finalData, RecordPrograms.state, SubexpSlotProgram.ports, hi.xEmpty,
              restrict, ports, h0]
          · simpa [finalData, RecordPrograms.state, SubexpSlotProgram.ports, h20, h21, h14]
              using hi.frame i hx h14 h20 h21
  have he := eval_call_lifted SubexpSlotProgram.program registers ports d
    registers_injective ports_injective ht
  rw [embed_restrict] at he
  refine ⟨n, embedState registers ports d finalData, hn, he, ?_⟩
  funext i
  by_cases hit : ∃ j, ports j = i
  · obtain ⟨j, rfl⟩ := hit
    rw [embedState_stack registers ports d finalData ports_injective, hs]
    change (Function.update (Function.update (restrict d).stacks 20 []) 14 (output D)) j =
      (Function.update (Function.update d.stacks (ports 20) []) (ports 14) (output D)) (ports j)
    simp [Function.update_apply, ports_injective.eq_iff, restrict]
  · rw [embedState_stack_frame registers ports d finalData i hit]
    have h110' : i ≠ 110 := fun h => hit ⟨20, by simpa [ports] using h.symm⟩
    have h14' : i ≠ 14 := fun h => hit ⟨14, by simpa [ports] using h.symm⟩
    simp [h110', h14']

def initializeOutput : Code := .base (.seq (.atom (.set 0 false))
  (.seq (.atom (.set 1 false)) (.seq (.atom (.set 2 false)) (.atom (.push 14 0)))))

def initialized (d : Data) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 false) 2 false,
    Function.update d.stacks 14 (false :: d.stacks 14)⟩

theorem initializeOutput_eval (d : Data) : Eval initializeOutput 4 d (initialized d) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 16) false) d).seq
    ((StructuredProgram.Eval.atom (.set (1 : Fin 16) false) _).seq
      ((StructuredProgram.Eval.atom (.set (2 : Fin 16) false) _).seq
        (StructuredProgram.Eval.atom (.push (14 : Fin 128) (0 : Fin 16)) _)))
  exact .base (by simpa [initialized, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using h)

def work : List (Fin 128) := [0, 4, 5, 6, 7, 8, 9, 10, 11, 110, 111, 112, 113, 114, 115, 116, 14]

def command : Code := .seq SubexpExponentSourceProgram.command (.seq initializeOutput slotCall)
def program := compiled command 2 14

def bound (D : ℕ) : ℕ :=
  25 * (3 * D + 2) * (3 * D + 1).choose D + 17 * D + 29 +
    RecordPrograms.budget (SubexpSlotProgram.callbackCost D (SubexpSymbolicCost.indexBits D))
      (SubexpSlotProgram.momentRecords D)

theorem program_runs (d : Data) (D : ℕ)
    (hD : d.stacks 2 = List.replicate D true)
    (hI : d.stacks 3 = List.replicate (SubexpSymbolicCost.indexBits D) true)
    (hwork : ∀ i ∈ work, d.stacks i = []) :
    ∃ e : Data, RunsIn program (bound D) (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = Function.update d.stacks 14 (output D) := by
  have hw : ∀ i ∈ SubexpExponentSourceProgram.work, d.stacks i = [] := by
    intro i hi
    apply hwork i
    simp only [SubexpExponentSourceProgram.work, work, List.mem_cons,
      List.not_mem_nil, or_false] at hi ⊢
    tauto
  obtain ⟨sn, s, hsn, hs, hss⟩ := SubexpExponentSourceProgram.command_eval d D hD hw
  let a := initialized s
  have ha := initializeOutput_eval s
  have hc : SubexpSlotProgram.Context (restrict a) D (SubexpSymbolicCost.indexBits D) := by
    constructor
    · simpa [restrict, ports, a, initialized, hss] using hD
    · simpa [restrict, ports, a, initialized, hss] using hI
    · intro i hi
      simp only [SubexpSlotProgram.work, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [restrict, ports, a, initialized, hss,
          hwork 4 (by decide), hwork 5 (by decide), hwork 6 (by decide), hwork 7 (by decide),
          hwork 8 (by decide), hwork 9 (by decide), hwork 10 (by decide), hwork 11 (by decide)]
  have hreg : ∀ i : Fin 3, a.regs (registers i) = false := by
    intro i; fin_cases i <;> simp [a, initialized, registers]
  have ha0 : a.stacks 0 = [] := by simp [a, initialized, hss, hwork 0 (by decide)]
  have ha111 : a.stacks 111 = [] := by simp [a, initialized, hss, hwork 111 (by decide)]
  have ha110 : a.stacks 110 = Encoding.encodeList id (SubexpSlotProgram.momentRecords D) := by
    simp [a, initialized, hss, SubexpExponentSourceProgram.output, SubexpSlotProgram.momentRecords_encode]
  have ha14 : a.stacks 14 = [false] := by simp [a, initialized, hss, hwork 14 (by decide)]
  obtain ⟨kn, e, hkn, hk, hks⟩ := slotCall_eval a D hc hreg ha0 ha111 ha110 ha14
  have total := hs.seq (ha.seq hk)
  refine ⟨e, ⟨sn + (4 + kn) + 1, ?_, compiled_halt_trace total 2 14⟩, ?_⟩
  · dsimp [bound]
    omega
  · rw [hks]
    funext i
    by_cases h110 : i = 110
    · subst i; simp [a, initialized, hss, hwork 110 (by decide)]
    by_cases h14 : i = 14
    · subst i; simp [a, initialized, hss]
    simp [a, initialized, hss, h110, h14]

theorem momentWord_length_le (D : ℕ) (bits : List Bool)
    (h : bits ∈ SubexpSlotProgram.momentRecords D) : bits.length ≤ 3 * D + 1 := by
  rcases List.mem_map.mp h with ⟨a, ha, rfl⟩
  have ha' := (Algorithm.mem_exponentList D (2 * D + 1) a).mp (List.mem_reverse.mp ha)
  simp only [SubexpExponentController.momentWord, SubexpSymbolicCost.unaryWords_length_exact,
    List.sum_ofFn, List.length_ofFn]
  omega

def callbackBound (D : ℕ) : ℕ :=
  D * (D + 1) * (100 * (5 * D + SubexpSymbolicCost.indexBits D + 2)) +
    13 * D ^ 2 + 46 * D + 24

theorem callbackCost_le (D : ℕ) (bits : List Bool) (h : bits.length ≤ 3 * D + 1) :
    SubexpSlotProgram.callbackCost D (SubexpSymbolicCost.indexBits D) bits ≤ callbackBound D := by
  calc
    _ ≤ D * (D + 1) * (100 * ((3 * D + 1) + 2 * D + SubexpSymbolicCost.indexBits D + 1)) +
        13 * D ^ 2 + 31 * D + 10 + 5 * (3 * D + 1) + 9 := by
      dsimp [SubexpSlotProgram.callbackCost, SubexpSlotProgram.gridCost]
      gcongr
    _ = callbackBound D := by unfold callbackBound; ring

private theorem budget_le_of_bounds (cost : List Bool → ℕ) (records : List (List Bool))
    (L C : ℕ) (hlen : ∀ bits ∈ records, bits.length ≤ L)
    (hcost : ∀ bits ∈ records, cost bits ≤ C) :
    RecordPrograms.budget cost records ≤ records.length * (6 * L + C + 7) := by
  induction records with
  | nil => simp [RecordPrograms.budget]
  | cons bits rest ih =>
    have hl := hlen bits (by simp)
    have hc := hcost bits (by simp)
    have hr := ih (fun x hx => hlen x (by simp [hx])) (fun x hx => hcost x (by simp [hx]))
    simp only [RecordPrograms.budget, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- The actual setup enumerates only the bounded-degree exponent family.
Its non-polynomial factor is the family cardinality, not a coordinate box. -/
theorem bound_le (D : ℕ) :
    bound D ≤ (3 * D + 1).choose D *
      (25 * (3 * D + 2) + callbackBound D + 18 * D + 13) + 17 * D + 29 := by
  have hb := budget_le_of_bounds
    (SubexpSlotProgram.callbackCost D (SubexpSymbolicCost.indexBits D))
    (SubexpSlotProgram.momentRecords D) (3 * D + 1) (callbackBound D)
    (momentWord_length_le D) (fun bits h => callbackCost_le D bits (momentWord_length_le D bits h))
  have hlen : (SubexpSlotProgram.momentRecords D).length = (3 * D + 1).choose D := by
    simp only [SubexpSlotProgram.momentRecords, List.length_map, List.length_reverse,
      Algorithm.exponentList_length]
    congr 1
    omega
  rw [hlen] at hb
  unfold bound
  nlinarith

end SubexponentialSAT.SubexpSlotSetup

end OAI.Algorithms
