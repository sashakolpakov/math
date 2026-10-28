import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.GatherProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-!
# Physical transpose read-plan generation

Two unary countdowns visit columns and rows in decreasing order. Each visit
constructs the unary physical index by repeated copying and emits one actual
framed record. Prepending these visits produces the increasing transpose
read order directly. All counters are runtime stacks and the code is fixed.
-/

namespace SubexponentialSAT.Subexp.BasisTransposePlanProgram

open BitProgram StructuredCalls

abbrev Data := State 3 7
abbrev Code := Cmd 3 7
def unary (n : ℕ) : List Bool := List.replicate n true

def ports (counter : Fin 7) : UnaryForPrograms.Ports 3 7 := ⟨counter, 0, 1⟩

def LoopFrame (base : Data) (counter output : Fin 7) (d : Data) : Prop :=
  ∀ i, i ≠ counter → i ≠ output → d.stacks i = base.stacks i

def downOutput (step : ℕ → List Bool → List Bool) : ℕ → List Bool → List Bool
  | 0, out => out
  | n + 1, out => downOutput step n (step n out)

def downBudget (cost : ℕ → ℕ) : ℕ → ℕ
  | 0 => 2
  | n + 1 => cost n + downBudget cost n + 2

/-- This specification contains a real evaluation of the fixed body for
each remaining counter value. It is instantiated below by copying and
framing programs, never by an opaque arithmetic callback. -/
def DownSpec (body : Code) (counter output : Fin 7)
    (step : ℕ → List Bool → List Bool) (cost : ℕ → ℕ) (base : Data) : Prop :=
  ∀ n d, LoopFrame base counter output d → d.stacks counter = unary n →
    ∃ t e, t ≤ cost n ∧ Eval body t d e ∧
      e.stacks = Function.update d.stacks output (step n (d.stacks output))

theorem down_visits (body : Code) (counter output : Fin 7) (hco : counter ≠ output)
    (step : ℕ → List Bool → List Bool) (cost : ℕ → ℕ) (base : Data)
    (spec : DownSpec body counter output step cost base) (n : ℕ) :
    ∀ d : Data, LoopFrame base counter output d → d.stacks counter = unary n →
      ∃ costs t e, UnaryForPrograms.Visits (ports counter) body costs t d e ∧
        t ≤ downBudget cost n ∧
        e.stacks = Function.update (Function.update d.stacks counter []) output
          (downOutput step n (d.stacks output)) := by
  induction n with
  | zero =>
    intro d hf hc
    refine ⟨[], 2, UnaryForPrograms.popped (ports counter) d,
      .done d hc, le_rfl, ?_⟩
    funext i
    by_cases hic : i = counter
    · subst i
      simp [UnaryForPrograms.popped, ports, downOutput, hc, unary, hco]
    by_cases hio : i = output
    · subst i
      simp [UnaryForPrograms.popped, ports, downOutput, hco.symm]
    · simp [UnaryForPrograms.popped, ports, downOutput, hic, hio]
  | succ n ih =>
    intro d hf hc
    let p := UnaryForPrograms.popped (ports counter) d
    have hp : p.stacks counter = unary n := by
      simp [p, UnaryForPrograms.popped, ports, hc, unary, List.replicate_succ]
    have hpf : LoopFrame base counter output p := by
      intro i hic hio
      simpa [p, UnaryForPrograms.popped, ports, hic] using hf i hic hio
    obtain ⟨nb, e, hnb, he, hes⟩ := spec n p hpf hp
    have hec : e.stacks counter = unary n := by simp [hes, hco, hp]
    have hef : LoopFrame base counter output e := by
      intro i hic hio
      simpa [hes, hio] using hpf i hic hio
    obtain ⟨costs, nt, f, hv, hnt, hfs⟩ := ih e hef hec
    have hcounter : e.stacks (ports counter).counter = p.stacks (ports counter).counter := by
      simp [hes, ports, hco]
    refine ⟨nb :: costs, nb + nt + 2, f,
      .step (by simp [ports, hc, unary]) he hcounter hv, ?_, ?_⟩
    · simp only [downBudget]
      omega
    · funext i
      by_cases hic : i = counter
      · subst i
        simp [hfs, hco]
      by_cases hio : i = output
      · subst i
        simp [hfs, hes, downOutput, p, UnaryForPrograms.popped, ports, hco.symm]
      · simp [hfs, hes, p, UnaryForPrograms.popped, ports, hic, hio]

theorem down_run (body : Code) (counter output : Fin 7) (hco : counter ≠ output)
    (step : ℕ → List Bool → List Bool) (cost : ℕ → ℕ) (base d : Data)
    (spec : DownSpec body counter output step cost base)
    (n : ℕ) (hf : LoopFrame base counter output d) (hc : d.stacks counter = unary n) :
    ∃ t e, Eval (UnaryForPrograms.forCmd (ports counter) body) t d e ∧
      t ≤ downBudget cost n ∧
      e.stacks = Function.update (Function.update d.stacks counter []) output
        (downOutput step n (d.stacks output)) := by
  obtain ⟨costs, t, e, hv, ht, hs⟩ := down_visits body counter output hco
    step cost base spec n d hf hc
  exact ⟨t, e, hv.eval, ht, hs⟩

theorem downBudget_le (cost : ℕ → ℕ) (n B : ℕ)
    (h : ∀ i, i < n → cost i ≤ B) : downBudget cost n ≤ n * (B + 2) + 2 := by
  induction n with
  | zero => simp [downBudget]
  | succ n ih =>
    have hn := h n (by omega)
    have ht := ih (fun i hi => h i (by omega))
    simp only [downBudget]
    nlinarith

def copy (src dst : Fin 7) : Code := .call (StackRoutines.copyProgram src dst 6 0 1)
abbrev copied (src dst : Fin 7) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

theorem copy_eval (src dst : Fin 7) (d : Data) (hsd : src ≠ dst)
    (hs6 : src ≠ 6) (hd6 : dst ≠ 6) (h6 : d.stacks 6 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (copied src dst d) :=
  .call _ (ListRegisterProgram.copy_run src dst 6 0 1 hsd hs6 hd6.symm
    (by decide) d.regs d.stacks h6)

theorem copied_stacks (src dst : Fin 7) (d : Data) :
    (copied src dst d).stacks =
      Function.update d.stacks dst (d.stacks src ++ d.stacks dst) := rfl

def multiply : Code := UnaryForPrograms.forCmd (ports 5) (copy 0 4)

theorem multiply_output (N n : ℕ) (out : List Bool) :
    downOutput (fun _ acc => unary N ++ acc) n out = unary (n * N) ++ out := by
  induction n generalizing out with
  | zero => simp [downOutput, unary]
  | succ n ih =>
    rw [downOutput, ih]
    simp only [unary, Nat.add_mul, one_mul]
    rw [← List.append_assoc, ← List.replicate_add]

theorem multiply_eval (N u : ℕ) (d : Data)
    (hN : d.stacks 0 = unary N) (hu : d.stacks 5 = unary u) (h6 : d.stacks 6 = []) :
    ∃ t e, Eval multiply t d e ∧ t ≤ u * (7 * N + 7) + 2 ∧
      e.stacks = Function.update (Function.update d.stacks 5 []) 4
        (unary (u * N) ++ d.stacks 4) := by
  have spec : DownSpec (copy 0 4) 5 4 (fun _ acc => unary N ++ acc)
      (fun _ => 7 * N + 5) d := by
    intro n a hf _
    have ha0 : a.stacks 0 = unary N := (hf 0 (by decide) (by decide)).trans hN
    have ha6 : a.stacks 6 = [] := (hf 6 (by decide) (by decide)).trans h6
    refine ⟨7 * (a.stacks 0).length + 5, copied 0 4 a, ?_,
      copy_eval 0 4 a (by decide) (by decide) (by decide) ha6, ?_⟩
    · simp [ha0, unary]
    ·
      rw [copied_stacks, ha0]
  obtain ⟨t, e, he, ht, hs⟩ := down_run (copy 0 4) 5 4 (by decide)
    (fun _ acc => unary N ++ acc) (fun _ => 7 * N + 5) d d spec u
    (fun _ _ _ => rfl) hu
  refine ⟨t, e, he, ?_, ?_⟩
  · have hb := downBudget_le (fun _ => 7 * N + 5) u (7 * N + 5) (by intros; exact le_rfl)
    simpa only [Nat.add_assoc] using ht.trans hb
  · simpa only [multiply_output] using hs

def emitStack : Fin 4 → Fin 7 := ![0, 6, 1, 4]
theorem emitStack_injective : Function.Injective emitStack := by decide
def emit : Code := .call (ProgramLinking.liftProgram SubexpNormalizeProgram.emitRecordProgram
  id emitStack)
def record (j : ℕ) : List Bool := true :: Encoding.frame (unary j)

theorem emit_eval (j : ℕ) (d : Data) (h4 : d.stacks 4 = unary j) :
    ∃ e : Data, Eval emit (5 * j + 7) d e ∧
      e.stacks = Function.update (Function.update d.stacks 4 []) 1 (record j ++ d.stacks 1) := by
  let a := SubexpNormalizeProgram.filterState (d.regs 0) (d.regs 1) (d.regs 2)
    (d.stacks 0) (d.stacks 6) (d.stacks 1) (unary j).reverse
  let b := SubexpNormalizeProgram.filterState true false (d.regs 2)
    (d.stacks 0) (d.stacks 6) (true :: (Encoding.frame (unary j) ++ d.stacks 1)) []
  have hp : projectState id emitStack d = a := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ emitStack, unary, h4, SubexpPostfixControl.quadruple]
  have ht := SubexpNormalizeProgram.emitRecord_trace (unary j)
    (d.stacks 0) (d.stacks 6) (d.stacks 1) (d.regs 0) (d.regs 1) (d.regs 2)
  have ht' : BitProgram.Trace SubexpNormalizeProgram.emitRecordProgram (5 * j + 7)
      (a.withPC (some SubexpNormalizeProgram.emitRecordProgram.entry))
      (b.withPC none) := by
    simpa only [a, b, unary, List.length_replicate] using ht
  have ht'' : BitProgram.Trace SubexpNormalizeProgram.emitRecordProgram (5 * j + 7)
      ((projectState id emitStack d).withPC (some SubexpNormalizeProgram.emitRecordProgram.entry))
      (b.withPC none) := by
    simpa only [hp] using ht'
  have he := eval_call_from_state SubexpNormalizeProgram.emitRecordProgram id emitStack d
    Function.injective_id emitStack_injective ht''
  let e := embedState id emitStack d b
  refine ⟨e, he, ?_⟩
  funext i
  by_cases hi : ∃ q, emitStack q = i
  · obtain ⟨q, rfl⟩ := hi
    rw [show e.stacks (emitStack q) = b.stacks q from
      embedState_stack _ _ _ _ emitStack_injective q]
    fin_cases q <;> simp [emitStack, b, record, SubexpNormalizeProgram.filterState,
      SubexpPostfixControl.quadruple]
  · have hi1 : i ≠ 1 := by intro h; apply hi; exact ⟨2, h.symm⟩
    have hi4 : i ≠ 4 := by intro h; apply hi; exact ⟨3, h.symm⟩
    rw [show e.stacks i = d.stacks i from embedState_stack_frame _ _ _ _ i hi]
    simp [hi1, hi4]

def entry : Code := .seq (copy 2 5) (.seq multiply (.seq (copy 3 4) emit))
def entryCost (N u z : ℕ) : ℕ :=
  (7 * u + 5) + (u * (7 * N + 7) + 2) + (7 * z + 5) + (5 * (u * N + z) + 7)

theorem entry_eval (N u z : ℕ) (d : Data) (hN : d.stacks 0 = unary N)
    (hu : d.stacks 2 = unary u) (hz : d.stacks 3 = unary z)
    (h4 : d.stacks 4 = []) (h5 : d.stacks 5 = []) (h6 : d.stacks 6 = []) :
    ∃ t e, Eval entry t d e ∧ t ≤ entryCost N u z ∧
      e.stacks = Function.update d.stacks 1 (record (u * N + z) ++ d.stacks 1) := by
  let a := copied 2 5 d
  have haN : a.stacks 0 = unary N := by simp [a, hN]
  have hau : a.stacks 5 = unary u := by simp [a, hu, h5]
  have ha6 : a.stacks 6 = [] := by simp [a, h6]
  obtain ⟨n, b, hb, hn, hbs⟩ := multiply_eval N u a haN hau ha6
  have hb4 : b.stacks 4 = unary (u * N) := by simp [hbs, a, h4]
  have hb3 : b.stacks 3 = unary z := by simp [hbs, a, hz]
  have hb6 : b.stacks 6 = [] := by simp [hbs, a, h6]
  let c := copied 3 4 b
  have hc4 : c.stacks 4 = unary (u * N + z) := by
    simp [c, hb3, hb4, unary, Nat.add_comm]
  obtain ⟨e, he, hes⟩ := emit_eval (u * N + z) c hc4
  refine ⟨(7 * (d.stacks 2).length + 5) +
    (n + ((7 * (b.stacks 3).length + 5) + (5 * (u * N + z) + 7))), e,
    (copy_eval 2 5 d (by decide) (by decide) (by decide) h6).seq
      (hb.seq ((copy_eval 3 4 b (by decide) (by decide) (by decide) hb6).seq he)), ?_, ?_⟩
  · simp only [hu, hb3, unary, List.length_replicate]
    unfold entryCost
    omega
  · funext i
    fin_cases i <;> simp [hes, c, hbs, a, h4, h5]

def recordPrefix (indices : List ℕ) : List Bool := indices.flatMap record
def rowIndices (N z r : ℕ) : List ℕ := (List.range r).map (fun u => u * N + z)
def columnIndices (N r : ℕ) : List ℕ :=
  (List.range r).flatMap (fun z => rowIndices N z N)
def plan (N : ℕ) : List ℕ := columnIndices N N
def planCode (N : ℕ) : List Bool :=
  ProgramEncoding.encodeRecords (GatherProgram.indexRecords (plan N))

theorem prefix_append (xs ys : List ℕ) : recordPrefix (xs ++ ys) = recordPrefix xs ++ recordPrefix ys := by
  simp [recordPrefix]

theorem row_output (N z r : ℕ) (out : List Bool) :
    downOutput (fun u acc => record (u * N + z) ++ acc) r out =
      recordPrefix (rowIndices N z r) ++ out := by
  induction r generalizing out with
  | zero => simp [downOutput, rowIndices, recordPrefix]
  | succ r ih =>
    rw [downOutput, ih]
    simp [rowIndices, List.range_succ, recordPrefix, List.append_assoc]

theorem column_output (N r : ℕ) (out : List Bool) :
    downOutput (fun z acc => recordPrefix (rowIndices N z N) ++ acc) r out =
      recordPrefix (columnIndices N r) ++ out := by
  induction r generalizing out with
  | zero => simp [downOutput, columnIndices, recordPrefix]
  | succ r ih =>
    rw [downOutput, ih]
    simp [columnIndices, List.range_succ, recordPrefix, List.append_assoc]

theorem encoded_prefix (indices : List ℕ) :
    ProgramEncoding.encodeRecords (GatherProgram.indexRecords indices) = recordPrefix indices ++ [false] := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
    simpa [ProgramEncoding.encodeRecords, GatherProgram.indexRecords, Encoding.encodeList,
      recordPrefix, record, unary, List.append_assoc] using
      congrArg (fun rest => record i ++ rest) ih

def inner : Code := UnaryForPrograms.forCmd (ports 2) entry
def row : Code := .seq (copy 0 2) inner
def rowCost (N z : ℕ) := 7 * N + 5 + downBudget (fun u => entryCost N u z) N

theorem row_eval (N z : ℕ) (d : Data) (hN : d.stacks 0 = unary N)
    (hz : d.stacks 3 = unary z) (h2 : d.stacks 2 = [])
    (h4 : d.stacks 4 = []) (h5 : d.stacks 5 = []) (h6 : d.stacks 6 = []) :
    ∃ t e, Eval row t d e ∧ t ≤ rowCost N z ∧
      e.stacks = Function.update d.stacks 1 (recordPrefix (rowIndices N z N) ++ d.stacks 1) := by
  let a := copied 0 2 d
  have haN : a.stacks 0 = unary N := by simp [a, hN]
  have ha2 : a.stacks 2 = unary N := by simp [a, hN, h2]
  have haz : a.stacks 3 = unary z := by simp [a, hz]
  have ha4 : a.stacks 4 = [] := by simp [a, h4]
  have ha5 : a.stacks 5 = [] := by simp [a, h5]
  have ha6 : a.stacks 6 = [] := by simp [a, h6]
  have spec : DownSpec entry 2 1 (fun u acc => record (u * N + z) ++ acc)
      (fun u => entryCost N u z) a := by
    intro u b hf hu
    obtain ⟨t, e, he, ht, hs⟩ := entry_eval N u z b
      ((hf 0 (by decide) (by decide)).trans haN) hu
      ((hf 3 (by decide) (by decide)).trans haz)
      ((hf 4 (by decide) (by decide)).trans ha4)
      ((hf 5 (by decide) (by decide)).trans ha5)
      ((hf 6 (by decide) (by decide)).trans ha6)
    exact ⟨t, e, ht, he, hs⟩
  obtain ⟨t, e, he, ht, hs⟩ := down_run entry 2 1 (by decide)
    (fun u acc => record (u * N + z) ++ acc) (fun u => entryCost N u z)
    a a spec N (fun _ _ _ => rfl) ha2
  refine ⟨7 * (d.stacks 0).length + 5 + t, e,
    (copy_eval 0 2 d (by decide) (by decide) (by decide) h6).seq he, ?_, ?_⟩
  · simp only [hN, unary, List.length_replicate]
    unfold rowCost
    omega
  · funext i
    fin_cases i <;> simp [hs, row_output, a, h2]

def outer : Code := UnaryForPrograms.forCmd (ports 3) row

theorem outer_eval (N : ℕ) (d : Data) (hN : d.stacks 0 = unary N)
    (h3 : d.stacks 3 = unary N) (h2 : d.stacks 2 = [])
    (h4 : d.stacks 4 = []) (h5 : d.stacks 5 = []) (h6 : d.stacks 6 = []) :
    ∃ t e, Eval outer t d e ∧ t ≤ downBudget (rowCost N) N ∧
      e.stacks = Function.update (Function.update d.stacks 3 []) 1
        (recordPrefix (plan N) ++ d.stacks 1) := by
  have spec : DownSpec row 3 1 (fun z acc => recordPrefix (rowIndices N z N) ++ acc)
      (rowCost N) d := by
    intro z a hf hz
    obtain ⟨t, e, he, ht, hs⟩ := row_eval N z a
      ((hf 0 (by decide) (by decide)).trans hN) hz
      ((hf 2 (by decide) (by decide)).trans h2)
      ((hf 4 (by decide) (by decide)).trans h4)
      ((hf 5 (by decide) (by decide)).trans h5)
      ((hf 6 (by decide) (by decide)).trans h6)
    exact ⟨t, e, ht, he, hs⟩
  obtain ⟨t, e, he, ht, hs⟩ := down_run row 3 1 (by decide)
    (fun z acc => recordPrefix (rowIndices N z N) ++ acc) (rowCost N)
    d d spec N (fun _ _ _ => rfl) h3
  exact ⟨t, e, he, ht, by simpa only [column_output, plan] using hs⟩

def start : Code := .seq (RecordPrograms.atom (.set 0 false))
  (RecordPrograms.atom (.push 1 0))
abbrev started (d : Data) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks 1 (false :: d.stacks 1)⟩

theorem start_eval (d : Data) : Eval start 2 d (started d) := by
  exact Eval.seq (.base (.atom _ _)) (.base (.atom _ _))

def reset : Code := .seq (RecordPrograms.atom (.set 0 false))
  (.seq (RecordPrograms.atom (.set 1 false)) (RecordPrograms.atom (.set 2 false)))
def resetState (d : Data) : Data := ⟨fun _ => false, d.stacks⟩

theorem reset_eval (d : Data) : Eval reset 3 d (resetState d) := by
  have h : Eval reset 3 d
      ((StructuredProgram.Atom.set 2 false).eval
        ((StructuredProgram.Atom.set 1 false).eval ((StructuredProgram.Atom.set 0 false).eval d))) :=
    Eval.seq (.base (.atom _ _)) (Eval.seq (.base (.atom _ _)) (.base (.atom _ _)))
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    fin_cases i <;> simp [ StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]
  · rfl

def command : Code := .seq start (.seq (copy 0 3) (.seq outer reset))
def commandBound (N : ℕ) := 2 + (7 * N + 5) + downBudget (rowCost N) N + 3
def runtimeBound (N : ℕ) := 200 * (N + 1) ^ 4

theorem command_eval (N : ℕ) (d : Data) (hN : d.stacks 0 = unary N)
    (h1 : d.stacks 1 = []) (h2 : d.stacks 2 = []) (h3 : d.stacks 3 = [])
    (h4 : d.stacks 4 = []) (h5 : d.stacks 5 = []) (h6 : d.stacks 6 = []) :
    ∃ t e, Eval command t d e ∧ t ≤ commandBound N ∧
      e.regs = (fun _ => false) ∧ e.stacks = Function.update d.stacks 1 (planCode N) := by
  let a := started d
  let b := copied 0 3 a
  have hbN : b.stacks 0 = unary N := by simp [b, a, hN]
  have hb3 : b.stacks 3 = unary N := by simp [b, a, hN, h3]
  have hb2 : b.stacks 2 = [] := by simp [b, a, h2]
  have hb4 : b.stacks 4 = [] := by simp [b, a, h4]
  have hb5 : b.stacks 5 = [] := by simp [b, a, h5]
  have hb6 : b.stacks 6 = [] := by simp [b, a, h6]
  obtain ⟨t, e, he, ht, hs⟩ := outer_eval N b hbN hb3 hb2 hb4 hb5 hb6
  have ha6 : a.stacks 6 = [] := by simp [a, h6]
  refine ⟨2 + ((7 * (a.stacks 0).length + 5) + (t + 3)), resetState e,
    (start_eval d).seq ((copy_eval 0 3 a (by decide) (by decide) (by decide) ha6).seq
      (he.seq (reset_eval e))), ?_, rfl, ?_⟩
  · have haN : a.stacks 0 = unary N := by simp [a, hN]
    simp only [haN, unary, List.length_replicate]
    unfold commandBound
    omega
  · change e.stacks = _
    funext i
    fin_cases i <;> simp [hs, b, a, h1, h3, planCode, encoded_prefix]

theorem entryCost_le (N u z : ℕ) (hu : u < N) (hz : z < N) :
    entryCost N u z ≤ 60 * (N + 1) ^ 2 := by
  have hmul := Nat.mul_le_mul_right N (Nat.le_of_lt hu)
  unfold entryCost
  nlinarith

theorem commandBound_le (N : ℕ) : commandBound N + 1 ≤ runtimeBound N := by
  let B := 60 * (N + 1) ^ 2
  have hrow : ∀ z, z < N → rowCost N z ≤ 7 * N + 5 + (N * (B + 2) + 2) := by
    intro z hz
    have h := downBudget_le (fun u => entryCost N u z) N B
      (fun u hu => entryCost_le N u z hu hz)
    unfold rowCost
    omega
  have ho := downBudget_le (rowCost N) N (7 * N + 5 + (N * (B + 2) + 2)) hrow
  unfold commandBound runtimeBound
  dsimp [B] at ho
  nlinarith [Nat.zero_le (N ^ 2), Nat.zero_le (N ^ 3), Nat.zero_le (N ^ 4)]

def program := compiled command 0 1
abbrev inputState (N : ℕ) (regs : Fin 3 → Bool) : Data :=
  ⟨regs, ![unary N, [], [], [], [], [], []]⟩
abbrev outputState (N : ℕ) : Data :=
  ⟨fun _ => false, ![unary N, planCode N, [], [], [], [], []]⟩

/-- The physical plan is emitted in forward transpose order. The unary
dimension is preserved, every scratch stack is empty, and all registers are
reset for the following gather call. -/
theorem program_run (N : ℕ) (regs : Fin 3 → Bool) :
    RunsIn program (runtimeBound N)
      ((inputState N regs).withPC (some program.entry)) ((outputState N).withPC none) := by
  obtain ⟨t, e, he, ht, hr, hs⟩ := command_eval N (inputState N regs)
    rfl rfl rfl rfl rfl rfl rfl
  have ho : e = outputState N := by
    cases e
    apply congrArg₂ StructuredProgram.State.mk
    · exact hr
    · funext i
      have hi := congrFun hs i
      fin_cases i <;> simpa [inputState, outputState] using hi
  subst e
  exact ⟨t + 1, (Nat.add_le_add_right ht 1).trans (commandBound_le N),
    compiled_halt_trace he 0 1⟩

theorem primitive_run (N : ℕ) (regs : Fin 3 → Bool) :
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program * runtimeBound N)
      (primitiveCfg program ((inputState N regs).withPC (some program.entry)))
      (primitiveCfg program ((outputState N).withPC none)) :=
  BitProgram.primitive_execution program (program_run N regs)

end SubexponentialSAT.Subexp.BasisTransposePlanProgram

end OAI.Algorithms
