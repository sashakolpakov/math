import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpGuardProgram
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace OAI.Algorithms

/-!
# Fixed-control guard for tuples of clause indices

Index words use the existing little-endian binary representation and tuples
use `Encoding.encodeList id`. The original tuple and the upper-bound word are
preserved while concrete comparisons check range and adjacent strict order.
-/

namespace SubexponentialSAT.TupleGuardProgram

open BitProgram StructuredCalls BinaryArithmetic

abbrev Data := State 13 9

abbrev moved (src dst : Fin 9) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩

abbrev move (src dst : Fin 9) : Cmd 13 9 :=
  .call (StackRoutines.transferProgram src dst 0 1)

theorem move_eval (src dst : Fin 9) (h : src ≠ dst) (d : Data) :
    Eval (move src dst) (3 * (d.stacks src).length + 3) d (moved src dst d) := by
  have ht := StackRoutines.transferProgram_trace src dst (0 : Fin 13) 1 h (by decide)
    d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ ht 3 rfl rfl
  apply Eval.call
  simpa [moved, StackRoutines.transferResult, StackRoutines.transferProgram,
    StructuredProgram.State.withPC, Nat.add_assoc] using hh

abbrev copied (src dst : Fin 9) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

abbrev copy (src dst : Fin 9) : Cmd 13 9 :=
  .call (StackRoutines.copyProgram src dst 8 0 1)

theorem copy_eval (src dst : Fin 9) (d : Data)
    (hsd : src ≠ dst) (hst : src ≠ 8) (htd : (8 : Fin 9) ≠ dst)
    (htmp : d.stacks 8 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (copied src dst d) := by
  have ht := StackRoutines.copyProgram_trace src dst 8 (0 : Fin 13) 1
    hsd hst htd (by decide) d.regs d.stacks htmp
  have hh := StackRoutines.halt_after_trace _ ht 7 rfl rfl
  apply Eval.call
  simpa [copied, StackRoutines.copyResult, StackRoutines.copyProgram,
    StructuredProgram.State.withPC, Nat.add_assoc] using hh

abbrev cleared (port : Fin 9) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks port d.stacks⟩

abbrev clear (port : Fin 9) : Cmd 13 9 := .call (StackRoutines.clearProgram port 0 1)

theorem clear_eval (port : Fin 9) (d : Data) :
    Eval (clear port) (2 * (d.stacks port).length + 3) d (cleared port d) := by
  have ht := StackRoutines.clearProgram_trace port (0 : Fin 13) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ ht 2 rfl rfl
  apply Eval.call
  simpa [cleared, StackRoutines.clearResult, StackRoutines.clearProgram,
    StructuredProgram.State.withPC, Nat.add_assoc] using hh

def workReg (i : Fin 8) : Fin 13 := Fin.castAdd 5 i
def pairPort (left right : Fin 9) (i : Fin 2) : Fin 9 := if i = 0 then left else right

theorem workReg_injective : Function.Injective workReg := Fin.castAdd_injective 8 5

theorem pairPort_injective (left right : Fin 9) (h : left ≠ right) :
    Function.Injective (pairPort left right) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [pairPort]

abbrev compare (left right : Fin 9) : Cmd 13 9 :=
  .call (ProgramLinking.liftProgram SubexpGuardProgram.Compare.program workReg (pairPort left right))

theorem compare_eval (left right : Fin 9) (h : left ≠ right) (d : Data) :
    ∃ e : Data,
      Eval (compare left right)
        (10 * max (d.stacks left).length (d.stacks right).length + 6) d e ∧
      e.regs 0 = decide (BinaryArithmetic.toNat (d.stacks left) < BinaryArithmetic.toNat (d.stacks right)) ∧
      (∀ i : Fin 13, 8 ≤ i.val → e.regs i = d.regs i) ∧
      (∀ i : Fin 9, i ≠ left → i ≠ right → e.stacks i = d.stacks i) ∧
      e.stacks left = [] ∧ e.stacks right = [] := by
  obtain ⟨e, he, ha, hr, hs, hz⟩ := SubexpGuardProgram.compare_call workReg
    (pairPort left right) workReg_injective (pairPort_injective left right h) d
  refine ⟨e, he, ?_, ?_, ?_, hz 0, hz 1⟩
  · apply Bool.eq_iff_iff.mpr
    simpa [workReg, pairPort] using ha
  · intro i hi
    apply hr
    rintro ⟨j, hj⟩
    have hjv := congrArg Fin.val hj
    change j.val = i.val at hjv
    have := j.isLt
    omega
  · intro i hl hr'
    apply hs
    rintro ⟨j, hj⟩
    fin_cases j <;> simp [pairPort] at hj <;> subst i <;> contradiction

abbrev range : Cmd 13 9 :=
  .seq (copy 5 6) (.seq (copy 3 7)
    (.seq (compare 6 7) (RecordPrograms.atom (.bnot 10 0))))

/-- The range test copies both operands, preserving every input stack. -/
theorem range_eval (bits bound : List Bool) (d : Data)
    (hbits : d.stacks 5 = bits) (hbound : d.stacks 3 = bound)
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = []) (h8 : d.stacks 8 = []) :
    ∃ n ≤ 20 * (bits.length + bound.length + 1), ∃ e : Data,
      Eval range n d e ∧ e.stacks = d.stacks ∧
      e.regs 10 = !decide (BinaryArithmetic.toNat bits < BinaryArithmetic.toNat bound) ∧
      (∀ i : Fin 13, 8 ≤ i.val → i ≠ 10 → e.regs i = d.regs i) := by
  let a := copied 5 6 d
  let b := copied 3 7 a
  have ha8 : a.stacks 8 = [] := by simpa [a, copied, StackRoutines.copyStacks] using h8
  have habound : a.stacks 3 = bound := by simpa [a, copied, StackRoutines.copyStacks] using hbound
  have hb6 : b.stacks 6 = bits := by simp [b, a, StackRoutines.copyStacks, hbits, h6]
  have hb7 : b.stacks 7 = bound := by simp [b, a, StackRoutines.copyStacks, hbound, h7]
  obtain ⟨e, he, he0, hr, hs, he6, he7⟩ := compare_eval 6 7 (by decide) b
  let f := (StructuredProgram.Atom.bnot (r := 13) (s := 9) 10 0).eval e
  refine ⟨(7 * (d.stacks 5).length + 5) + ((7 * (a.stacks 3).length + 5) +
    ((10 * max (b.stacks 6).length (b.stacks 7).length + 6) + 1)), ?_, f, ?_, ?_, ?_, ?_⟩
  · rw [hbits, habound, hb6, hb7]
    have hm := max_le (Nat.le_add_right bits.length bound.length)
      (Nat.le_add_left bound.length bits.length)
    omega
  · exact Eval.seq (copy_eval 5 6 d (by decide) (by decide) (by decide) h8)
      (Eval.seq (copy_eval 3 7 a (by decide) (by decide) (by decide) ha8)
        (Eval.seq he (.base (.atom _ _))))
  · change e.stacks = d.stacks
    funext i
    by_cases hi6 : i = 6
    · subst i; exact he6.trans h6.symm
    by_cases hi7 : i = 7
    · subst i; exact he7.trans h7.symm
    simpa [b, a, copied, StackRoutines.copyStacks, hi6, hi7] using hs i hi6 hi7
  · simp [f, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, he0, hb6, hb7]
  · intro i hi hne
    have hh := hr i hi
    have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
    have hi1 : i ≠ 1 := by intro h; subst i; simp at hi
    simpa [f, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr,
      hne, b, a, copied, readRegs, hi0, hi1] using hh

abbrev previousLess : Option (List Bool) → List Bool → Bool
  | none, _ => true
  | some previous, bits => decide (BinaryArithmetic.toNat previous < BinaryArithmetic.toNat bits)

abbrev adjacent : Cmd 13 9 :=
  .ite 11
    (.seq (copy 5 7) (.seq (compare 4 7)
      (.seq (RecordPrograms.atom (.bnot 0 0)) (RecordPrograms.atom (.bor 10 10 0)))))
    (RecordPrograms.atom (.set 11 true))

/-- Adjacent comparison consumes the old previous word. The first tuple
entry instead initializes the finite Boolean "have previous" flag. -/
theorem adjacent_eval (previous : Option (List Bool)) (bits : List Bool) (d : Data)
    (hprev : d.stacks 4 = previous.getD []) (hflag : d.regs 11 = previous.isSome)
    (hbits : d.stacks 5 = bits) (h7 : d.stacks 7 = []) (h8 : d.stacks 8 = []) :
    ∃ n ≤ 20 * ((previous.getD []).length + bits.length + 1), ∃ e : Data,
      Eval adjacent n d e ∧ e.stacks = Function.update d.stacks 4 [] ∧
      e.regs 10 = (d.regs 10 || !previousLess previous bits) ∧ e.regs 11 = true ∧
      e.regs 8 = d.regs 8 ∧ e.regs 9 = d.regs 9 := by
  cases previous with
  | none =>
    let e := (StructuredProgram.Atom.set (r := 13) (s := 9) 11 true).eval d
    refine ⟨2, by simp; omega, e, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Eval.ite_false hflag (.base (.atom _ _))
    · change d.stacks = Function.update d.stacks 4 []
      change d.stacks 4 = [] at hprev
      rw [← hprev]
      simp
    · simp [e, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, previousLess]
    · simp [e, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]
    · simp [e, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]
    · simp [e, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]
  | some previous =>
    let a := copied 5 7 d
    have ha4 : a.stacks 4 = previous := by simpa [a, copied, StackRoutines.copyStacks] using hprev
    have ha7 : a.stacks 7 = bits := by simp [a, StackRoutines.copyStacks, hbits, h7]
    obtain ⟨e, he, he0, hr, hs, he4, he7⟩ := compare_eval 4 7 (by decide) a
    let f := (StructuredProgram.Atom.bor (r := 13) (s := 9) 10 10 0).eval
      ((StructuredProgram.Atom.bnot (r := 13) (s := 9) 0 0).eval e)
    refine ⟨((7 * (d.stacks 5).length + 5) +
      ((10 * max (a.stacks 4).length (a.stacks 7).length + 6) + (1 + 1))) + 1,
      ?_, f, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hbits, ha4, ha7]
      simp only [Option.getD_some]
      have hm := max_le (Nat.le_add_right previous.length bits.length)
        (Nat.le_add_left bits.length previous.length)
      omega
    · exact Eval.ite_true hflag
        (Eval.seq (copy_eval 5 7 d (by decide) (by decide) (by decide) h8)
          (Eval.seq he (Eval.seq (.base (.atom _ _)) (.base (.atom _ _)))))
    · change e.stacks = Function.update d.stacks 4 []
      funext i
      by_cases hi4 : i = 4
      · subst i; simpa using he4
      by_cases hi7 : i = 7
      · subst i; simpa [h7] using he7
      simpa [a, copied, StackRoutines.copyStacks, hi4, hi7] using hs i hi4 hi7
    · have hh := hr 10 (by decide)
      simp [a, readRegs] at hh
      simp [f, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr,
        previousLess, he0, ha4, ha7, hh]
    · have hh := hr 11 (by decide)
      simpa [f, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr,
        a, copied, readRegs, hflag] using hh
    · have hh := hr 8 (by decide)
      simpa [f, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr,
        a, copied, readRegs] using hh
    · have hh := hr 9 (by decide)
      simpa [f, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr,
        a, copied, readRegs] using hh

def stepGood (bound : List Bool) (previous : Option (List Bool)) (bits : List Bool) : Bool :=
  decide (BinaryArithmetic.toNat bits < BinaryArithmetic.toNat bound) && previousLess previous bits

def ready (tuple bound : List Bool) (previous : Option (List Bool)) (d : Data) : Prop :=
  d.stacks 0 = tuple ∧ d.stacks 3 = bound ∧ d.stacks 4 = previous.getD [] ∧
    d.regs 11 = previous.isSome ∧ d.stacks 5 = [] ∧ d.stacks 6 = [] ∧
    d.stacks 7 = [] ∧ d.stacks 8 = []

abbrev callback : Cmd 13 9 :=
  .seq (move 2 5) (.seq range (.seq adjacent (.seq (move 5 2) (move 2 4))))

theorem callback_eval (tuple bound : List Bool) (previous : Option (List Bool))
    (bits : List Bool) (d : Data) (hd : ready tuple bound previous d)
    (hin : d.stacks 2 = bits.reverse) :
    ∃ n ≤ 100 * (bits.length + bound.length + (previous.getD []).length + 1),
      ∃ e : Data, Eval callback n d e ∧ ready tuple bound (some bits) e ∧
        e.stacks 1 = d.stacks 1 ∧ e.stacks 2 = [] ∧
        e.regs 8 = d.regs 8 ∧ e.regs 9 = d.regs 9 ∧
        e.regs 10 = !stepGood bound previous bits := by
  rcases hd with ⟨h0, h3, h4, h11, h5, h6, h7, h8⟩
  let a := moved 2 5 d
  have ha5 : a.stacks 5 = bits := by simp [a, StackRoutines.transferStacks, hin, h5]
  have ha3 : a.stacks 3 = bound := by simpa [a, moved, StackRoutines.transferStacks] using h3
  have ha6 : a.stacks 6 = [] := by simpa [a, moved, StackRoutines.transferStacks] using h6
  have ha7 : a.stacks 7 = [] := by simpa [a, moved, StackRoutines.transferStacks] using h7
  have ha8 : a.stacks 8 = [] := by simpa [a, moved, StackRoutines.transferStacks] using h8
  obtain ⟨n, hn, b, hb, hbst, hb10, hbreg⟩ := range_eval bits bound a ha5 ha3 ha6 ha7 ha8
  have hb4 : b.stacks 4 = previous.getD [] := by
    simpa [hbst, a, moved, StackRoutines.transferStacks] using h4
  have hb11 : b.regs 11 = previous.isSome := by
    simpa [a, moved, readRegs, h11] using hbreg 11 (by decide) (by decide)
  have hb5 : b.stacks 5 = bits := by simpa [hbst] using ha5
  have hb7 : b.stacks 7 = [] := by simpa [hbst] using ha7
  have hb8 : b.stacks 8 = [] := by simpa [hbst] using ha8
  obtain ⟨m, hm, c, hc, hcst, hc10, hc11, hc8, hc9⟩ :=
    adjacent_eval previous bits b hb4 hb11 hb5 hb7 hb8
  have hc5 : c.stacks 5 = bits := by simp [hcst, hb5]
  have hc2 : c.stacks 2 = [] := by simp [hcst, hbst, a, StackRoutines.transferStacks]
  have hc4 : c.stacks 4 = [] := by simp [hcst]
  let e := moved 2 4 (moved 5 2 c)
  have he_stacks : e.stacks = Function.update (Function.update d.stacks 2 []) 4 bits := by
    funext i
    fin_cases i <;>
      simp [e, StackRoutines.transferStacks, hcst, hbst, a, hin, h5]
  have he_ready : ready tuple bound (some bits) e := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [he_stacks] using h0
    · simpa [he_stacks] using h3
    · simp [he_stacks]
    · simpa [e, moved, readRegs] using hc11
    · simpa [he_stacks] using h5
    · simpa [he_stacks] using h6
    · simpa [he_stacks] using h7
    · simpa [he_stacks] using h8
  refine ⟨(3 * (d.stacks 2).length + 3) + (n + (m +
    ((3 * (c.stacks 5).length + 3) + (3 * ((moved 5 2 c).stacks 2).length + 3)))),
    ?_, e, ?_, he_ready, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hin, List.length_reverse, hc5]
    simp only [ StackRoutines.transferStacks, Function.update_self, hc5, hc2,
      List.append_nil, List.length_reverse]
    omega
  · exact Eval.seq (move_eval 2 5 (by decide) d)
      (Eval.seq hb (Eval.seq hc
        (Eval.seq (move_eval 5 2 (by decide) c) (move_eval 2 4 (by decide) (moved 5 2 c)))))
  · simp [he_stacks]
  · simp [he_stacks]
  · have hh := (hc8.trans (hbreg 8 (by decide) (by decide)))
    simpa [e, a, moved, readRegs] using hh
  · have hh := (hc9.trans (hbreg 9 (by decide) (by decide)))
    simpa [e, a, moved, readRegs] using hh
  · simpa [e, moved, readRegs, hb10, stepGood, Bool.not_and] using hc10

def ports : RecordPrograms.Ports 13 9 where
  tag := 8
  present := 9
  found := 10
  source := 1
  payload := 2
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

theorem ready_state (tuple bound : List Bool) (previous : Option (List Bool))
    (base : Data) (v pr f : Bool) (src out : List Bool) :
    ready tuple bound previous (RecordPrograms.state ports base v pr f src out) ↔
      ready tuple bound previous base := by
  simp [ready, RecordPrograms.state, ports]

theorem callback_record (tuple bound : List Bool) (previous : Option (List Bool))
    (bits tail : List Bool) (base : Data) (hbase : ready tuple bound previous base) :
    ∃ n ≤ 100 * (bits.length + bound.length + (previous.getD []).length + 1),
      ∃ e : Data, ready tuple bound (some bits) e ∧
        Eval callback n (RecordPrograms.state ports base false true false tail bits.reverse)
          (RecordPrograms.state ports e false true (!stepGood bound previous bits) tail []) := by
  let d := RecordPrograms.state ports base false true false tail bits.reverse
  have hd : ready tuple bound previous d := (ready_state _ _ _ _ _ _ _ _ _).mpr hbase
  have hin : d.stacks 2 = bits.reverse := by simp [d, RecordPrograms.state, ports]
  obtain ⟨n, hn, e, he, hr, hs, hp, ht, hpr, hb⟩ := callback_eval tuple bound previous bits d hd hin
  have heq : RecordPrograms.state ports e false true (!stepGood bound previous bits) tail [] = e := by
    apply RecordPrograms.state_eq_self
    · simpa [d, RecordPrograms.state, ports] using ht
    · simpa [d, RecordPrograms.state, ports] using hpr
    · exact hb
    · simpa [d, RecordPrograms.state, ports] using hs
    · exact hp
  refine ⟨n, hn, e, hr, ?_⟩
  rw [heq]
  exact he

/-- Semantic specification of range and strict adjacent order. -/
def goodFrom (bound : List Bool) : Option (List Bool) → List (List Bool) → Bool
  | _, [] => true
  | previous, bits :: rest => stepGood bound previous bits && goodFrom bound (some bits) rest

def unread (bound : List Bool) : Option (List Bool) → List (List Bool) → List Bool
  | _, [] => []
  | previous, bits :: rest =>
      if stepGood bound previous bits then unread bound (some bits) rest
      else Encoding.encodeList id rest

def recordCost (bound : List Bool) (width : ℕ) (bits : List Bool) : ℕ :=
  100 * (bits.length + bound.length + width + 1)

/-- The loop uses the preceding word stored on tape. Neither its value nor the
tuple length is represented by the finite control. -/
theorem loop_eval (tuple bound : List Bool) (width : ℕ)
    (words : List (List Bool)) (hwidth : ∀ bits ∈ words, bits.length ≤ width)
    (previous : Option (List Bool)) (hp : (previous.getD []).length ≤ width)
    (base : Data) (hbase : ready tuple bound previous base) :
    ∃ n ≤ 1 + RecordPrograms.budget (recordCost bound width) words,
      ∃ previous' : Option (List Bool), ∃ e : Data,
        ready tuple bound previous' e ∧ (previous'.getD []).length ≤ width ∧
        Eval (RecordPrograms.loop ports callback) n (RecordPrograms.afterTag ports base words [])
          (RecordPrograms.state ports e false true (!goodFrom bound previous words)
            (unread bound previous words) []) := by
  induction words generalizing previous base with
  | nil =>
    refine ⟨1, by simp [RecordPrograms.budget], previous, base, hbase, hp, ?_⟩
    apply Eval.while_false
    simp [RecordPrograms.afterTag]
  | cons bits rest ih =>
    have hw : bits.length ≤ width := hwidth bits (by simp)
    have hrest : ∀ b ∈ rest, b.length ≤ width := by
      intro b hb
      exact hwidth b (by simp [hb])
    let tail := Encoding.encodeList id rest
    obtain ⟨n, hn, middle, hm, hcallback⟩ := callback_record tuple bound previous bits tail base hbase
    have hn' : n ≤ recordCost bound width bits := by dsimp [recordCost]; omega
    have hreader : Eval (RecordPrograms.reader ports) (6 * bits.length + 4)
        (RecordPrograms.afterTag ports base (bits :: rest) [])
        (RecordPrograms.state ports base false true false tail bits.reverse) := by
      simpa [RecordPrograms.afterTag, tail] using
        RecordPrograms.reader_eval ports base bits tail [] true true false
    have hguard : (RecordPrograms.afterTag ports base (bits :: rest) []).regs ports.tag = true := by
      simp [RecordPrograms.afterTag]
    cases hg : stepGood bound previous bits with
    | false =>
      have hbranch : Eval
          (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
            (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
          (RecordPrograms.state ports middle false true (!stepGood bound previous bits) tail [])
          (RecordPrograms.state ports middle false true true tail []) := by
        rw [hg]
        apply Eval.ite_true (by simp)
        exact RecordPrograms.set_tag_eval ports middle false true true false tail []
      have hfinish : Eval (RecordPrograms.loop ports callback) 1
          (RecordPrograms.state ports middle false true true tail [])
          (RecordPrograms.state ports middle false true true tail []) :=
        Eval.while_false (by simp)
      have hr := Eval.while_true hguard (Eval.seq hreader (Eval.seq hcallback hbranch)) hfinish
      refine ⟨(6 * bits.length + 4 + (n + 2)) + 1 + 1, ?_, some bits, middle, hm, hw, ?_⟩
      · simp only [RecordPrograms.budget]
        omega
      · simpa [RecordPrograms.loop, RecordPrograms.body, goodFrom, unread, hg, tail] using hr
    | true =>
      have hbranch : Eval
          (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
            (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
          (RecordPrograms.state ports middle false true (!stepGood bound previous bits) tail [])
          (RecordPrograms.afterTag ports middle rest []) := by
        rw [hg]
        apply Eval.ite_false (by simp)
        simpa [tail] using RecordPrograms.pop_list_eval ports middle rest [] false true
      obtain ⟨m, hmn, previous', e, he, hprev, hloop⟩ :=
        ih hrest (some bits) hw middle hm
      have hr := Eval.while_true hguard (Eval.seq hreader (Eval.seq hcallback hbranch)) hloop
      refine ⟨(6 * bits.length + 4 + (n + 2)) + m + 1, ?_, previous', e, he, hprev, ?_⟩
      · simp only [RecordPrograms.budget]
        omega
      · simpa [RecordPrograms.loop, RecordPrograms.body, goodFrom, unread, hg] using hr

theorem iterate_eval (tuple bound : List Bool) (width : ℕ)
    (words : List (List Bool)) (hwidth : ∀ bits ∈ words, bits.length ≤ width)
    (previous : Option (List Bool)) (hp : (previous.getD []).length ≤ width)
    (base : Data) (hbase : ready tuple bound previous base) (v pr f : Bool) :
    ∃ n ≤ 3 + RecordPrograms.budget (recordCost bound width) words,
      ∃ previous' : Option (List Bool), ∃ e : Data,
        ready tuple bound previous' e ∧ (previous'.getD []).length ≤ width ∧
        Eval (RecordPrograms.iterate ports callback) n
          (RecordPrograms.state ports base v pr f (Encoding.encodeList id words) [])
          (RecordPrograms.state ports e false true (!goodFrom bound previous words)
            (unread bound previous words) []) := by
  obtain ⟨n, hn, previous', e, he, hprev, hloop⟩ :=
    loop_eval tuple bound width words hwidth previous hp base hbase
  refine ⟨1 + (1 + n), by omega, previous', e, he, hprev, ?_⟩
  apply Eval.seq (RecordPrograms.set_found_eval ports base v pr f false _ [])
  apply Eval.seq _ hloop
  simpa using RecordPrograms.pop_list_eval ports base words [] v pr

theorem unread_length_le (bound : List Bool) (previous : Option (List Bool))
    (words : List (List Bool)) :
    (unread bound previous words).length ≤ (Encoding.encodeList id words).length := by
  induction words generalizing previous with
  | nil => simp [unread]
  | cons bits rest ih =>
    cases h : stepGood bound previous bits <;>
      simp [unread, h, Encoding.length_encodeList_cons]
    exact (ih _).trans (by omega)

theorem record_length_le (words : List (List Bool)) (bits : List Bool) (h : bits ∈ words) :
    bits.length ≤ (Encoding.encodeList id words).length := by
  induction words with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    simp only [Encoding.length_encodeList_cons, id_eq]
    rcases h with rfl | h
    · omega
    · have := ih h
      omega

theorem budget_le (bound : List Bool) (width : ℕ) (words : List (List Bool)) :
    RecordPrograms.budget (recordCost bound width) words ≤
      200 * (bound.length + width + 1) * (Encoding.encodeList id words).length := by
  induction words with
  | nil => simp [RecordPrograms.budget]
  | cons bits rest ih =>
    have hstep : 6 * bits.length + recordCost bound width bits + 7 ≤
        200 * (bound.length + width + 1) * (2 * bits.length + 2) := by
      dsimp [recordCost]
      nlinarith
    simp only [RecordPrograms.budget, Encoding.length_encodeList_cons, id_eq]
    nlinarith

def workEmpty (d : Data) : Prop :=
  d.stacks 1 = [] ∧ d.stacks 2 = [] ∧ d.stacks 4 = [] ∧ d.stacks 5 = [] ∧
    d.stacks 6 = [] ∧ d.stacks 7 = [] ∧ d.stacks 8 = []

abbrev started (d : Data) : Data :=
  (StructuredProgram.Atom.set (r := 13) (s := 9) 11 false).eval (copied 0 1 d)

abbrev finished (d : Data) : Data :=
  (StructuredProgram.Atom.bnot (r := 13) (s := 9) 10 10).eval (cleared 4 (cleared 1 d))

abbrev command : Cmd 13 9 :=
  .seq (copy 0 1) (.seq (RecordPrograms.atom (.set 11 false))
    (.seq (RecordPrograms.iterate ports callback)
      (.seq (clear 1) (.seq (clear 4) (RecordPrograms.atom (.bnot 10 10))))))

/-- The program table is fixed, independent of tuple length and word width. -/
def program := compiled command 0 0

def bound (limit : List Bool) (words : List (List Bool)) : ℕ :=
  240 * (limit.length + (Encoding.encodeList id words).length + 1) *
    ((Encoding.encodeList id words).length + 1)

/-- Exact input and output ports for use as an odometer-body guard. The
original tuple and limit are preserved, and every work stack is emptied. -/
theorem command_eval (limit : List Bool) (words : List (List Bool)) (d : Data)
    (htuple : d.stacks 0 = Encoding.encodeList id words) (hlimit : d.stacks 3 = limit)
    (hwork : workEmpty d) :
    ∃ n, n + 1 ≤ bound limit words ∧ ∃ e : Data, Eval command n d e ∧
      e.stacks 0 = Encoding.encodeList id words ∧ e.stacks 3 = limit ∧ workEmpty e ∧
      e.regs 10 = goodFrom limit none words := by
  rcases hwork with ⟨h1, h2, h4, h5, h6, h7, h8⟩
  let a := started d
  have ha : ready (Encoding.encodeList id words) limit none a := by
    simp [a, StackRoutines.copyStacks, ready,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr,
      htuple, hlimit, h4, h5, h6, h7, h8]
  have ha1 : a.stacks 1 = Encoding.encodeList id words := by
    simp [a, StackRoutines.copyStacks,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, htuple, h1]
  have ha2 : a.stacks 2 = [] := by
    simpa [a, started, copied, StackRoutines.copyStacks,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using h2
  obtain ⟨m, hm, previous, b, hb, hp, he⟩ :=
    iterate_eval (Encoding.encodeList id words) limit (Encoding.encodeList id words).length
      words (record_length_le words) none (by simp) a ha (a.regs 8) (a.regs 9) (a.regs 10)
  have hstart : RecordPrograms.state ports a (a.regs 8) (a.regs 9) (a.regs 10)
      (Encoding.encodeList id words) [] = a :=
    RecordPrograms.state_eq_self ports a _ _ _ _ _ rfl rfl rfl ha1 ha2
  rw [hstart] at he
  let c := RecordPrograms.state ports b false true (!goodFrom limit none words)
    (unread limit none words) []
  have hc : ready (Encoding.encodeList id words) limit previous c :=
    (ready_state _ _ _ _ _ _ _ _ _).mpr hb
  have hc1 : c.stacks 1 = unread limit none words := by simp [c, RecordPrograms.state, ports]
  have hc2 : c.stacks 2 = [] := by simp [c, RecordPrograms.state, ports]
  have hc4 : c.stacks 4 = previous.getD [] := hc.2.2.1
  have hc10 : c.regs 10 = !goodFrom limit none words := by simp [c, RecordPrograms.state, ports]
  refine ⟨(7 * (d.stacks 0).length + 5) + (1 + (m +
    ((2 * (c.stacks 1).length + 3) + ((2 * (c.stacks 4).length + 3) + 1)))),
    ?_, finished c, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htuple, hc1, hc4]
    have hu := unread_length_le limit none words
    have hbudget := budget_le limit (Encoding.encodeList id words).length words
    dsimp [bound]
    nlinarith only [hm, hu, hbudget, hp, Nat.zero_le limit.length,
      Nat.zero_le (Encoding.encodeList id words).length]
  · apply Eval.seq (copy_eval 0 1 d (by decide) (by decide) (by decide) h8)
    apply Eval.seq (.base (.atom _ _))
    apply Eval.seq he
    apply Eval.seq (clear_eval 1 c)
    have hf : Eval (RecordPrograms.atom (.bnot 10 10)) 1
        (cleared 4 (cleared 1 c)) (finished c) := .base (.atom _ _)
    simpa [cleared, StackRoutines.clearStacks] using Eval.seq (clear_eval 4 (cleared 1 c)) hf
  · simpa [finished, cleared, StackRoutines.clearStacks,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using hc.1
  · simpa [finished, cleared, StackRoutines.clearStacks,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using hc.2.1
  · rcases hc with ⟨_, _, _, _, hc5, hc6, hc7, hc8⟩
    simp [workEmpty, finished, StackRoutines.clearStacks,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr,
      hc2, hc5, hc6, hc7, hc8]
  · simp [finished, readRegs, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, hc10]

theorem program_runsIn (limit : List Bool) (words : List (List Bool)) (d : Data)
    (htuple : d.stacks 0 = Encoding.encodeList id words) (hlimit : d.stacks 3 = limit)
    (hwork : workEmpty d) :
    ∃ e : Data, RunsIn program (bound limit words)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks 0 = Encoding.encodeList id words ∧ e.stacks 3 = limit ∧ workEmpty e ∧
      e.regs 10 = goodFrom limit none words := by
  obtain ⟨n, hn, e, he, ht, hl, hw, hg⟩ := command_eval limit words d htuple hlimit hwork
  exact ⟨e, ⟨n + 1, hn, compiled_halt_trace he 0 0⟩, ht, hl, hw, hg⟩

theorem primitive_execution (limit : List Bool) (words : List (List Bool)) (d : Data)
    (htuple : d.stacks 0 = Encoding.encodeList id words) (hlimit : d.stacks 3 = limit)
    (hwork : workEmpty d) :
    ∃ e : Data, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * bound limit words)
      (primitiveCfg program (d.withPC (some program.entry)))
      (primitiveCfg program (e.withPC none)) ∧
      e.stacks 0 = Encoding.encodeList id words ∧ e.stacks 3 = limit ∧ workEmpty e ∧
      e.regs 10 = goodFrom limit none words := by
  obtain ⟨e, he, ht, hl, hw, hg⟩ := program_runsIn limit words d htuple hlimit hwork
  exact ⟨e, BitProgram.primitive_execution program he, ht, hl, hw, hg⟩

/-- Transitivity turns the checked adjacent inequalities into strict ordering
of every pair of distinct positions in the tuple. -/
theorem goodFrom_true_iff (limit : List Bool) (previous : Option (List Bool))
    (words : List (List Bool)) :
    goodFrom limit previous words = true ↔
      (∀ bits ∈ words, BinaryArithmetic.toNat bits < BinaryArithmetic.toNat limit) ∧
      words.Pairwise (fun x y => BinaryArithmetic.toNat x < BinaryArithmetic.toNat y) ∧
      (∀ p, previous = some p → ∀ bits ∈ words, BinaryArithmetic.toNat p < BinaryArithmetic.toNat bits) := by
  induction words generalizing previous with
  | nil => simp [goodFrom]
  | cons bits rest ih =>
    rw [goodFrom, Bool.and_eq_true, stepGood, Bool.and_eq_true, decide_eq_true_eq, ih]
    simp only [List.forall_mem_cons, List.pairwise_cons]
    constructor
    · rintro ⟨⟨hrange, hprevious⟩, hrest, hpairs, hfrom⟩
      have hhead : ∀ x ∈ rest, BinaryArithmetic.toNat bits < BinaryArithmetic.toNat x := hfrom bits rfl
      refine ⟨⟨hrange, hrest⟩, ⟨hhead, hpairs⟩, ?_⟩
      intro p hp
      subst previous
      have hpb : BinaryArithmetic.toNat p < BinaryArithmetic.toNat bits := by simpa [previousLess] using hprevious
      exact ⟨hpb, fun x hx => Nat.lt_trans hpb (hhead x hx)⟩
    · rintro ⟨⟨hrange, hrest⟩, ⟨hhead, hpairs⟩, hprevious⟩
      refine ⟨⟨hrange, ?_⟩, hrest, hpairs, ?_⟩
      · cases previous with
        | none => rfl
        | some p => simpa [previousLess] using (hprevious p rfl).1
      · intro p hp
        have hbp : bits = p := Option.some.inj hp
        subst p
        exact hhead

theorem goodFrom_none_iff (limit : List Bool) (words : List (List Bool)) :
    goodFrom limit none words = true ↔
      (∀ bits ∈ words, BinaryArithmetic.toNat bits < BinaryArithmetic.toNat limit) ∧
      words.Pairwise (fun x y => BinaryArithmetic.toNat x < BinaryArithmetic.toNat y) := by
  simpa using goodFrom_true_iff limit none words

/-- Complete actual guard contract, including the numeric range and ordering
meaning of its result flag. Empty tuples are accepted. -/
theorem guard_correct (limit : List Bool) (words : List (List Bool)) (d : Data)
    (htuple : d.stacks 0 = Encoding.encodeList id words) (hlimit : d.stacks 3 = limit)
    (hwork : workEmpty d) :
    ∃ e : Data, RunsIn program (bound limit words)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks 0 = Encoding.encodeList id words ∧ e.stacks 3 = limit ∧ workEmpty e ∧
      (e.regs 10 = true ↔ (∀ bits ∈ words, BinaryArithmetic.toNat bits < BinaryArithmetic.toNat limit) ∧
        words.Pairwise (fun x y => BinaryArithmetic.toNat x < BinaryArithmetic.toNat y)) := by
  obtain ⟨e, he, ht, hl, hw, hg⟩ := program_runsIn limit words d htuple hlimit hwork
  refine ⟨e, he, ht, hl, hw, ?_⟩
  rw [hg, goodFrom_none_iff]

/-- Quadratic in the total number of input bits, with no machine-word access
or input-dependent control state hidden in the cost. -/
theorem bound_le_square (limit : List Bool) (words : List (List Bool)) :
    bound limit words ≤
      240 * (limit.length + (Encoding.encodeList id words).length + 1) ^ 2 := by
  unfold bound
  nlinarith

end SubexponentialSAT.TupleGuardProgram

end OAI.Algorithms
