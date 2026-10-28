import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram

namespace OAI.Algorithms

/-! Actual parsing and record-order preparation of the two plans in a pair
payload. Registers 0, 1, and 2 are scratch; all other registers are framed. -/

namespace SubexponentialSAT.Subexp.PairPlanPreparation

open BitProgram StackRoutines StructuredCalls

abbrev Data := StructuredProgram.State 16 34

private theorem state_ext {r s : ℕ} {a b : StructuredProgram.State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; cases hr; cases hs; rfl

private theorem embedState_eq {r s R S : ℕ}
    (reg : Fin r → Fin R) (stack : Fin s → Fin S)
    (hreg : Function.Injective reg) (hstack : Function.Injective stack)
    (frame target : StructuredProgram.State R S) (source : StructuredProgram.State r s)
    (hr : ∀ i, target.regs (reg i) = source.regs i)
    (hs : ∀ i, target.stacks (stack i) = source.stacks i)
    (hfr : ∀ j, (¬ ∃ i, reg i = j) → target.regs j = frame.regs j)
    (hfs : ∀ j, (¬ ∃ i, stack i = j) → target.stacks j = frame.stacks j) :
    embedState reg stack frame source = target := by
  apply state_ext
  · funext j
    by_cases hj : ∃ i, reg i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [embedState_register reg stack frame source hreg]
      exact (hr i).symm
    · rw [embedState_register_frame reg stack frame source j hj]
      exact (hfr j hj).symm
  · funext j
    by_cases hj : ∃ i, stack i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [embedState_stack reg stack frame source hstack]
      exact (hs i).symm
    · rw [embedState_stack_frame reg stack frame source j hj]
      exact (hfs j hj).symm

abbrev transfer (src dst : Fin 34) : Cmd 16 34 := .call (transferProgram src dst 0 1)
def transferred (a : Data) (src dst : Fin 34) : Data :=
  ⟨readRegs a.regs 0 1 none, transferStacks src dst a.stacks⟩

theorem transfer_eval (a : Data) (src dst : Fin 34) (hne : src ≠ dst) :
    Eval (transfer src dst) (3 * (a.stacks src).length + 3) a (transferred a src dst) := by
  apply Eval.call
  have h := halt_after_trace _
    (transferProgram_trace src dst (0 : Fin 16) 1 hne (by decide) a.regs a.stacks) 3 rfl rfl
  simpa [transfer, transferred, transferResult, transferProgram,
    StructuredProgram.State.withPC, Nat.add_assoc] using h

abbrev clear (src : Fin 34) : Cmd 16 34 := .call (clearProgram src 0 1)
def cleared (a : Data) (src : Fin 34) : Data :=
  ⟨readRegs a.regs 0 1 none, clearStacks src a.stacks⟩

theorem clear_eval (a : Data) (src : Fin 34) :
    Eval (clear src) (2 * (a.stacks src).length + 3) a (cleared a src) := by
  apply Eval.call
  have h := halt_after_trace _ (clearProgram_trace src (0 : Fin 16) 1 a.regs a.stacks) 2 rfl rfl
  simpa [clear, cleared, clearResult, clearProgram,
    StructuredProgram.State.withPC, Nat.add_assoc] using h

abbrev copy (src dst : Fin 34) : Cmd 16 34 := .call (copyProgram src dst 1 0 1)
def copied (a : Data) (src dst : Fin 34) : Data :=
  ⟨readRegs a.regs 0 1 none, copyStacks src dst a.stacks⟩

theorem copy_eval (a : Data) (src dst : Fin 34) (hsd : src ≠ dst)
    (hs1 : src ≠ 1) (h1d : (1 : Fin 34) ≠ dst) (ht : a.stacks 1 = []) :
    Eval (copy src dst) (7 * (a.stacks src).length + 5) a (copied a src dst) := by
  apply Eval.call
  have h := halt_after_trace _
    (copyProgram_trace src dst (1 : Fin 34) (0 : Fin 16) 1 hsd hs1 h1d
      (by decide) a.regs a.stacks ht) 7 rfl rfl
  simpa [copy, copied, copyResult, copyProgram,
    StructuredProgram.State.withPC, Nat.add_assoc] using h

def fieldPorts : RecordPrograms.Ports 16 34 :=
  ⟨0, 1, 2, 22, 23, by decide, by decide, by decide, by decide⟩

def fieldRead (a : Data) (bits tail : List Bool) : Data :=
  RecordPrograms.state fieldPorts a false true (a.regs 2) tail (bits.reverse ++ a.stacks 23)

theorem readField_eval (a : Data) (bits tail : List Bool)
    (hin : a.stacks 22 = Encoding.frame bits ++ tail) :
    Eval (RecordPrograms.reader fieldPorts) (6 * bits.length + 4) a (fieldRead a bits tail) := by
  have h := RecordPrograms.reader_eval fieldPorts a bits tail (a.stacks 23)
    (a.regs 0) (a.regs 1) (a.regs 2)
  have he : RecordPrograms.state fieldPorts a (a.regs 0) (a.regs 1) (a.regs 2)
      (Encoding.frame bits ++ tail) (a.stacks 23) = a :=
    RecordPrograms.state_eq_self fieldPorts a _ _ _ _ _ rfl rfl rfl hin rfl
  simpa only [he, fieldRead] using h

def pairPayload (left right : List (List Bool)) : List Bool :=
  Encoding.frame (ProgramEncoding.encodeRecords left) ++
    Encoding.frame (ProgramEncoding.encodeRecords right)

abbrev parsePair : Cmd 16 34 :=
  .seq (transfer 21 22) (.seq (RecordPrograms.reader fieldPorts)
    (.seq (transfer 23 24) (.seq (RecordPrograms.reader fieldPorts) (transfer 23 25))))

def parsed (a : Data) (left right : List (List Bool)) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update (Function.update (Function.update
      (Function.update a.stacks 21 []) 22 []) 23 []) 24 (ProgramEncoding.encodeRecords left))
      25 (ProgramEncoding.encodeRecords right)⟩

def parseCost (left right : List (List Bool)) : ℕ :=
  3 * (pairPayload left right).length +
    9 * ((ProgramEncoding.encodeRecords left).length + (ProgramEncoding.encodeRecords right).length) + 17

theorem parsePair_eval (a : Data) (left right : List (List Bool))
    (hin : a.stacks 21 = (pairPayload left right).reverse)
    (h22 : a.stacks 22 = []) (h23 : a.stacks 23 = [])
    (h24 : a.stacks 24 = []) (h25 : a.stacks 25 = []) :
    Eval parsePair (parseCost left right) a (parsed a left right) := by
  let l := ProgramEncoding.encodeRecords left
  let r := ProgramEncoding.encodeRecords right
  let a1 := transferred a 21 22
  let a2 := fieldRead a1 l (Encoding.frame r)
  let a3 := transferred a2 23 24
  let a4 := fieldRead a3 r []
  let a5 := transferred a4 23 25
  have t0 := transfer_eval a 21 22 (by decide)
  have t1 := readField_eval a1 l (Encoding.frame r)
    (by simp [a1, transferred, transferStacks, hin, h22, pairPayload, l, r])
  have t2 := transfer_eval a2 23 24 (by decide)
  have t3 := readField_eval a3 r []
    (by simp [a3, transferred, transferStacks, a2, fieldRead, RecordPrograms.state, fieldPorts])
  have t4 := transfer_eval a4 23 25 (by decide)
  have he : a5 = parsed a left right := by
    apply state_ext
    · funext j; fin_cases j <;> simp [a5, a4, a3, a2, a1, fieldRead, transferred,
        RecordPrograms.state, fieldPorts, readRegs, parsed]
    · funext j; fin_cases j <;> simp [a5, a4, a3, a2, a1, fieldRead, transferred,
        RecordPrograms.state, fieldPorts, transferStacks, parsed, h22, h23, h24, h25, l, r]
  have t := t0.seq (t1.seq (t2.seq (t3.seq t4)))
  change transferred a4 23 25 = parsed a left right at he
  rw [he] at t
  convert t using 1
  simp [a4, a3, a2, a1, fieldRead, transferred, RecordPrograms.state, fieldPorts,
    transferStacks, hin, h22, h23, h24, l, r, parseCost]
  ring

theorem parsed_register_frame (a : Data) (left right : List (List Bool)) (j : Fin 16)
    (hj : 3 ≤ j.val) : (parsed a left right).regs j = a.regs j := by
  have h0 : j ≠ 0 := by intro h; subst j; norm_num at hj
  have h1 : j ≠ 1 := by intro h; subst j; norm_num at hj
  simp [parsed, readRegs, h0, h1]

theorem parsed_stack_frame (a : Data) (left right : List (List Bool)) (j : Fin 34)
    (h21 : j ≠ 21) (h22 : j ≠ 22) (h23 : j ≠ 23) (h24 : j ≠ 24) (h25 : j ≠ 25) :
    (parsed a left right).stacks j = a.stacks j := by simp [parsed, h21, h22, h23, h24, h25]

def smallRegs : Fin 3 → Fin 16 := Fin.castAdd 13
def reversePorts (src dst : Fin 34) : Fin 4 → Fin 34 := ![src, 1, dst, 4]

theorem smallRegs_injective : Function.Injective smallRegs := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 16 => k.val) h)

abbrev reverseRecords (src dst : Fin 34) : Cmd 16 34 :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.reverseRecordsProgram
    smallRegs (reversePorts src dst))

def reversed (a : Data) (src dst : Fin 34) (out : List Bool) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 0 false) 1 true) 2 false,
    Function.update (Function.update a.stacks src []) dst out⟩

theorem reverse_eval (a : Data) (src dst : Fin 34)
    (hi : Function.Injective (reversePorts src dst)) (records acc : List (List Bool))
    (hin : a.stacks src = ProgramEncoding.encodeRecords records)
    (hacc : a.stacks dst = ProgramEncoding.encodeRecords acc) (h4 : a.stacks 4 = []) :
    ∃ n ≤ 10 * (ProgramEncoding.encodeRecords records).length,
      Eval (reverseRecords src dst) n a
        (reversed a src dst (ProgramEncoding.encodeRecords (records.reverse ++ acc))) := by
  have hs1 : src ≠ 1 := by simpa [reversePorts] using hi.ne (show (0 : Fin 4) ≠ 1 by decide)
  have hsd : src ≠ dst := by simpa [reversePorts] using hi.ne (show (0 : Fin 4) ≠ 2 by decide)
  have hs4 : src ≠ 4 := by simpa [reversePorts] using hi.ne (show (0 : Fin 4) ≠ 3 by decide)
  have hd1 : dst ≠ 1 := by simpa [reversePorts] using hi.ne (show (2 : Fin 4) ≠ 1 by decide)
  have hd4 : dst ≠ 4 := by simpa [reversePorts] using hi.ne (show (2 : Fin 4) ≠ 3 by decide)
  let x := SubexpNormalizeProgram.filterState (a.regs 0) (a.regs 1) (a.regs 2)
    (ProgramEncoding.encodeRecords records) (a.stacks 1) (ProgramEncoding.encodeRecords acc) []
  let y := SubexpNormalizeProgram.filterState false true false [] (a.stacks 1)
    (ProgramEncoding.encodeRecords (records.reverse ++ acc)) []
  have hx : embedState smallRegs (reversePorts src dst) a x = a := by
    apply embedState_eq _ _ smallRegs_injective hi
    · intro i; fin_cases i <;> simp [x, smallRegs, SubexpNormalizeProgram.filterState]
    · intro i; fin_cases i <;> simp [x, reversePorts, SubexpNormalizeProgram.filterState, hin, hacc, h4]
    · intros; rfl
    · intros; rfl
  have hy : embedState smallRegs (reversePorts src dst) a y =
      reversed a src dst (ProgramEncoding.encodeRecords (records.reverse ++ acc)) := by
    apply embedState_eq _ _ smallRegs_injective hi
    · intro i; fin_cases i <;> simp [y, smallRegs, reversed, SubexpNormalizeProgram.filterState]
    · intro i; fin_cases i <;> simp [y, reversePorts, reversed, SubexpNormalizeProgram.filterState,
        hsd, Ne.symm hs1, Ne.symm hs4, Ne.symm hd1, Ne.symm hd4, h4]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [smallRegs] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [smallRegs] using h.symm⟩
      have h2 : j ≠ 2 := fun h => hj ⟨2, by simpa [smallRegs] using h.symm⟩
      simp [reversed, h0, h1, h2]
    · intro j hj
      have hs : j ≠ src := fun h => hj ⟨0, by simpa [reversePorts] using h.symm⟩
      have hd : j ≠ dst := fun h => hj ⟨2, by simpa [reversePorts] using h.symm⟩
      simp [reversed, hs, hd]
  obtain ⟨n, hn, ht⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records acc [] (a.stacks 1)
    (a.regs 0) (a.regs 1) (a.regs 2)
  have ht' : Trace SubexpNormalizeProgram.reverseRecordsProgram n
      (x.withPC (some SubexpNormalizeProgram.reverseRecordsProgram.entry)) (y.withPC none) := by
    simpa only [x, y, ProgramEncoding.encodeRecords, Encoding.encodeList,
      List.append_nil] using ht
  have he := eval_call_lifted SubexpNormalizeProgram.reverseRecordsProgram smallRegs
    (reversePorts src dst) a smallRegs_injective hi ht'
  exact ⟨n, hn, by simpa only [hx, hy, reverseRecords] using he⟩

theorem reversed_register_frame (a : Data) (src dst : Fin 34) (out : List Bool) (j : Fin 16)
    (hj : 3 ≤ j.val) : (reversed a src dst out).regs j = a.regs j := by
  have h0 : j ≠ 0 := by intro h; subst j; norm_num at hj
  have h1 : j ≠ 1 := by intro h; subst j; norm_num at hj
  have h2 : j ≠ 2 := by intro h; subst j; norm_num at hj
  simp [reversed, h0, h1, h2]

theorem reversed_stack_frame (a : Data) (src dst : Fin 34) (out : List Bool) (j : Fin 34)
    (hs : j ≠ src) (hd : j ≠ dst) : (reversed a src dst out).stacks j = a.stacks j := by
  simp [reversed, hs, hd]

/-- Prepare the concatenated union of the two vertex plans for filtering. -/
abbrev buildUnion : Cmd 16 34 :=
  .seq (copy 25 6) (.seq (copy 24 0) (reverseRecords 0 6))

def unionPrepared (a : Data) (left right : List (List Bool)) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 0 false) 1 true) 2 false,
    Function.update a.stacks 6 (ProgramEncoding.encodeRecords (left.reverse ++ right))⟩

theorem buildUnion_eval (a : Data) (left right : List (List Bool))
    (hl : a.stacks 24 = ProgramEncoding.encodeRecords left)
    (hr : a.stacks 25 = ProgramEncoding.encodeRecords right)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = [])
    (h4 : a.stacks 4 = []) (h6 : a.stacks 6 = []) :
    ∃ n ≤ 17 * (ProgramEncoding.encodeRecords left).length +
        7 * (ProgramEncoding.encodeRecords right).length + 10,
      Eval buildUnion n a (unionPrepared a left right) := by
  let a1 := copied a 25 6
  let a2 := copied a1 24 0
  have t0 := copy_eval a 25 6 (by decide) (by decide) (by decide) h1
  have t1 := copy_eval a1 24 0 (by decide) (by decide) (by decide)
    (by simp [a1, copied, copyStacks, h1])
  obtain ⟨n, hn, t2⟩ := reverse_eval a2 0 6 (by decide) left right
    (by simp [a2, a1, copied, copyStacks, hl, h0])
    (by simp [a2, a1, copied, copyStacks, hr, h6])
    (by simp [a2, a1, copied, copyStacks, h4])
  have he : reversed a2 0 6 (ProgramEncoding.encodeRecords (left.reverse ++ right)) =
      unionPrepared a left right := by
    apply state_ext
    · funext j; fin_cases j <;> simp [a2, a1, reversed, copied, readRegs, unionPrepared]
    · funext j; fin_cases j <;> simp [a2, a1, reversed, copied, copyStacks, unionPrepared, h0]
  rw [he] at t2
  refine ⟨_, ?_, t0.seq (t1.seq t2)⟩
  have he24 : a1.stacks 24 = ProgramEncoding.encodeRecords left := by
    simp [a1, copied, copyStacks, hl]
  rw [hr, he24]
  omega

theorem unionPrepared_register_frame (a : Data) (left right : List (List Bool))
    (j : Fin 16) (hj : 3 ≤ j.val) : (unionPrepared a left right).regs j = a.regs j := by
  exact reversed_register_frame a 0 6 [] j hj

theorem unionPrepared_stack_frame (a : Data) (left right : List (List Bool))
    (j : Fin 34) (hj : j ≠ 6) : (unionPrepared a left right).stacks j = a.stacks j := by
  simp [unionPrepared, hj]

abbrev seedOutputs : Cmd 16 34 := .base
  (.seq (.atom (.set 0 false)) (.seq (.atom (.push 6 0)) (.atom (.push 9 0))))

def seeded (a : Data) : Data :=
  ⟨Function.update a.regs 0 false,
    Function.update (Function.update a.stacks 6 (false :: a.stacks 6)) 9 (false :: a.stacks 9)⟩

theorem seedOutputs_eval (a : Data) : Eval seedOutputs 3 a (seeded a) := by
  have t0 := StructuredProgram.Eval.atom (StructuredProgram.Atom.set 0 false) a
  have t1 := StructuredProgram.Eval.atom (StructuredProgram.Atom.push 6 0)
    ((StructuredProgram.Atom.set 0 false).eval a)
  have t2 := StructuredProgram.Eval.atom (StructuredProgram.Atom.push 9 0)
    ((StructuredProgram.Atom.push 6 0).eval ((StructuredProgram.Atom.set 0 false).eval a))
  simpa [seedOutputs, seeded, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using
    Eval.base (t0.seq (t1.seq t2))

/-- Produce the reversed query-record lists required by the selector mapper.
Existing union/filter data in stacks 6 and 9 is explicitly cleared first. -/
abbrev reverseQueries : Cmd 16 34 :=
  .seq (clear 6) (.seq (clear 9) (.seq seedOutputs
    (.seq (reverseRecords 24 6) (reverseRecords 25 9))))

def queriesPrepared (a : Data) (left right : List (List Bool)) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 0 false) 1 true) 2 false,
    Function.update (Function.update (Function.update (Function.update a.stacks
      6 (ProgramEncoding.encodeRecords left.reverse))
      9 (ProgramEncoding.encodeRecords right.reverse)) 24 []) 25 []⟩

theorem reverseQueries_eval (a : Data) (left right : List (List Bool))
    (hl : a.stacks 24 = ProgramEncoding.encodeRecords left)
    (hr : a.stacks 25 = ProgramEncoding.encodeRecords right)
    (h4 : a.stacks 4 = []) :
    ∃ n ≤ 2 * (a.stacks 6).length + 2 * (a.stacks 9).length +
        10 * (ProgramEncoding.encodeRecords left).length +
        10 * (ProgramEncoding.encodeRecords right).length + 9,
      Eval reverseQueries n a (queriesPrepared a left right) := by
  let a1 := cleared a 6
  let a2 := cleared a1 9
  let a3 := seeded a2
  let a4 := reversed a3 24 6 (ProgramEncoding.encodeRecords left.reverse)
  have t0 := clear_eval a 6
  have t1 := clear_eval a1 9
  have t2 := seedOutputs_eval a2
  obtain ⟨n3, hn3, t3⟩ := reverse_eval a3 24 6 (by decide) left []
    (by simp [a3, a2, a1, seeded, cleared, clearStacks, hl])
    (by simp [a3, a2, a1, seeded, cleared, clearStacks, ProgramEncoding.encodeRecords,
      Encoding.encodeList])
    (by simp [a3, a2, a1, seeded, cleared, clearStacks, h4])
  simp only [List.append_nil] at t3
  obtain ⟨n4, hn4, t4⟩ := reverse_eval a4 25 9 (by decide) right []
    (by simp [a4, a3, a2, a1, reversed, seeded, cleared, clearStacks, hr])
    (by simp [a4, a3, a2, a1, reversed, seeded, cleared, clearStacks,
      ProgramEncoding.encodeRecords, Encoding.encodeList])
    (by simp [a4, a3, a2, a1, reversed, seeded, cleared, clearStacks, h4])
  simp only [List.append_nil] at t4
  have he : reversed a4 25 9 (ProgramEncoding.encodeRecords right.reverse) =
      queriesPrepared a left right := by
    apply state_ext
    · funext j; fin_cases j <;> simp [a4, a3, a2, a1, reversed, seeded, cleared,
        readRegs, queriesPrepared]
    · funext j; fin_cases j <;> simp [a4, a3, a2, a1, reversed, seeded, cleared,
        clearStacks, queriesPrepared]
  rw [he] at t4
  refine ⟨_, ?_, t0.seq (t1.seq (t2.seq (t3.seq t4)))⟩
  have he9 : a1.stacks 9 = a.stacks 9 := by simp [a1, cleared, clearStacks]
  rw [he9]
  omega

theorem queriesPrepared_register_frame (a : Data) (left right : List (List Bool))
    (j : Fin 16) (hj : 3 ≤ j.val) : (queriesPrepared a left right).regs j = a.regs j := by
  exact reversed_register_frame a 0 6 [] j hj

theorem queriesPrepared_stack_frame (a : Data) (left right : List (List Bool))
    (j : Fin 34) (h6 : j ≠ 6) (h9 : j ≠ 9) (h24 : j ≠ 24) (h25 : j ≠ 25) :
    (queriesPrepared a left right).stacks j = a.stacks j := by
  simp [queriesPrepared, h6, h9, h24, h25]

end SubexponentialSAT.Subexp.PairPlanPreparation

end OAI.Algorithms
