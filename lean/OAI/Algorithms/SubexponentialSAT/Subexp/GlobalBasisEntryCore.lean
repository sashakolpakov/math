import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CollisionStreamProgram
import OAI.Algorithms.SubexponentialSAT.SubexpScalarCellRead
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-! Concrete framed-word, comparison, and scalar-cell services for the
global matrix entry callback. Register 6 is the persistent row-kind flag. -/

namespace SubexponentialSAT.Subexp.GlobalBasisEntryCore

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 16 32
abbrev Code := Cmd 16 32
abbrev Store := Fin 32 → List Bool

def unary (n : ℕ) : List Bool := List.replicate n true

@[simp] theorem unary_length (n : ℕ) : (unary n).length = n := by simp [unary]
@[simp] theorem unary_reverse (n : ℕ) : (unary n).reverse = unary n := by simp [unary]
@[simp] theorem unary_inj (a b : ℕ) : unary a = unary b ↔ a = b := by
  constructor
  · intro h
    simpa using congrArg List.length h
  · rintro rfl; rfl

def copy (src dst : Fin 32) : Code := .call (StackRoutines.copyProgram src dst 31 0 1)
def transfer (src dst : Fin 32) : Code := .call (StackRoutines.transferProgram src dst 0 1)
def clear (src : Fin 32) : Code := .call (StackRoutines.clearProgram src 0 1)

def cleared (src : Fin 32) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩

theorem clear_eval (src : Fin 32) (d : Data) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared src d) :=
  .call _ (ListRegisterProgram.clear_run src (0 : Fin 16) 1 d.regs d.stacks)

def fieldPorts (dst : Fin 32) (hd : (16 : Fin 32) ≠ dst) : RecordPrograms.Ports 16 32 where
  tag := 0
  present := 1
  found := 2
  source := 16
  payload := dst
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := hd

def readField (dst : Fin 32) (hd : (16 : Fin 32) ≠ dst) : Code :=
  RecordPrograms.reader (fieldPorts dst hd)

theorem readField_eval (dst : Fin 32) (hd : (16 : Fin 32) ≠ dst)
    (d : Data) (n : ℕ) (tail : List Bool)
    (hs : d.stacks 16 = Encoding.frame (unary n) ++ tail) (he : d.stacks dst = []) :
    ∃ e, Eval (readField dst hd) (6 * n + 4) d e ∧
      e.stacks = Function.update (Function.update d.stacks 16 tail) dst (unary n) ∧
      e.regs 6 = d.regs 6 ∧ e.regs 7 = d.regs 7 := by
  let p := fieldPorts dst hd
  let e := RecordPrograms.state p d false true (d.regs 2) tail (unary n)
  have hstart : RecordPrograms.state p d (d.regs 0) (d.regs 1) (d.regs 2)
      (Encoding.frame (unary n) ++ tail) [] = d :=
    RecordPrograms.state_eq_self p d _ _ _ _ _ rfl rfl rfl hs he
  have h := RecordPrograms.reader_eval p d (unary n) tail [] (d.regs 0) (d.regs 1) (d.regs 2)
  rw [hstart] at h
  refine ⟨e, ?_, rfl, ?_, ?_⟩
  · change Eval (RecordPrograms.reader p) (6 * n + 4) d e
    simpa only [unary_length, unary_reverse, List.append_nil] using h
  · simp [e, RecordPrograms.state, p, fieldPorts]
  · simp [e, RecordPrograms.state, p, fieldPorts]

def pop (src : Fin 32) : Code := .base (.atom (.pop src 7 0))
def popped (src : Fin 32) (bit : Bool) (tail : List Bool) (d : Data) : Data :=
  ⟨readRegs d.regs 7 0 (some bit), Function.update d.stacks src tail⟩

theorem pop_eval (src : Fin 32) (d : Data) (bit : Bool) (tail : List Bool)
    (hs : d.stacks src = bit :: tail) : Eval (pop src) 1 d (popped src bit tail d) := by
  have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.pop src 7 0) d
  simpa [pop, popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, hs] using Eval.base h

def smallRegs : Fin 5 ↪ Fin 16 := ⟨Fin.castAdd 11, Fin.castAdd_injective 5 11⟩
def sealPorts : Fin 13 ↪ Fin 32 := ⟨fun i => ⟨16 + i.val, by omega⟩, by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp at this
  omega⟩

theorem smallRegs_ne_six (i : Fin 5) : smallRegs i ≠ 6 := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = 6 at hv
  omega

def sealCall : Code := liftCommand CollisionStreamProgram.sealCommand 1 11 smallRegs sealPorts

theorem sealCall_eval (d : Data) :
    ∃ n e, n ≤ 11 * (d.stacks 17).length + 2 * (d.stacks 28).length + 20 ∧
      Eval sealCall n d e ∧
      e.stacks = Function.update (Function.update (Function.update d.stacks 17 []) 28 [])
        27 (decide (d.stacks 17 = d.stacks 28) :: d.stacks 27) ∧
      e.regs 6 = d.regs 6 := by
  let a := projectState smallRegs sealPorts d
  obtain ⟨n, hn, he⟩ := CollisionStreamProgram.seal_eval a
  let b := CollisionStreamProgram.sealed a (decide (a.stacks 1 = a.stacks 12))
  let e := embedState smallRegs sealPorts d b
  have hn' : n ≤ 11 * (d.stacks 17).length + 2 * (d.stacks 28).length + 19 := by
    change n ≤ 11 * (d.stacks 17).length + 2 * (d.stacks 28).length + 19 at hn
    exact hn
  refine ⟨n + 1, e, by omega,
    eval_liftCommand_from_state CollisionStreamProgram.sealCommand 1 11 smallRegs sealPorts d
      smallRegs.injective sealPorts.injective he, ?_, ?_⟩
  · change Function.extend sealPorts b.stacks d.stacks = _
    dsimp [b, CollisionStreamProgram.sealed]
    rw [ProgramLinking.extend_update sealPorts.injective,
      ProgramLinking.extend_update sealPorts.injective,
      ProgramLinking.extend_update sealPorts.injective]
    have hb := congrArg StructuredProgram.State.stacks
      (embedState_project smallRegs sealPorts d smallRegs.injective sealPorts.injective)
    change Function.extend sealPorts a.stacks d.stacks = d.stacks at hb
    rw [hb]
    rfl
  · exact embedState_register_frame smallRegs sealPorts d b 6 (by
      rintro ⟨i, hi⟩
      exact smallRegs_ne_six i hi)

theorem low_ne_high (i j : Fin 32) (hi : i.val < 16) (hj : 16 ≤ j.val) : i ≠ j := by
  intro h
  subst j
  omega

def compare (left right : Fin 32) : Code :=
  .seq (copy left 17) (.seq (copy right 28) (.seq sealCall (pop 27)))

theorem compare_eval (left right : Fin 32) (hl : left.val < 16) (hr : right.val < 16)
    (d : Data) (h17 : d.stacks 17 = []) (h28 : d.stacks 28 = [])
    (h27 : d.stacks 27 = []) (h31 : d.stacks 31 = []) :
    ∃ n e, n ≤ 18 * (d.stacks left).length + 9 * (d.stacks right).length + 31 ∧
      Eval (compare left right) n d e ∧ e.stacks = d.stacks ∧
      e.regs 6 = d.regs 6 ∧ e.regs 7 = decide (d.stacks left = d.stacks right) := by
  have hl17 := low_ne_high left 17 hl (by decide)
  have hl31 := low_ne_high left 31 hl (by decide)
  have hr17 := low_ne_high right 17 hr (by decide)
  have hr28 := low_ne_high right 28 hr (by decide)
  have hr31 := low_ne_high right 31 hr (by decide)
  let a := afterCopy d left 17 0 1
  let b := afterCopy a right 28 0 1
  have ha := SubexpScanPrimitives.copy_eval d left 17 31 0 1
    hl17 hl31 (by decide) (by decide) h31
  have hb := SubexpScanPrimitives.copy_eval a right 28 31 0 1
    hr28 hr31 (by decide) (by decide) (by simp [a, afterCopy, StackRoutines.copyStacks, h31])
  have haRight : a.stacks right = d.stacks right := by
    simp [a, afterCopy, StackRoutines.copyStacks, hr17]
  have hb17 : b.stacks 17 = d.stacks left := by
    simp [b, a, afterCopy, StackRoutines.copyStacks, h17]
  have hb28 : b.stacks 28 = d.stacks right := by
    simp [b, a, afterCopy, StackRoutines.copyStacks, h28, hr17]
  have hb27 : b.stacks 27 = [] := by
    simp [b, a, afterCopy, StackRoutines.copyStacks, h27]
  obtain ⟨n, c, hn, hc, hcs, hc6⟩ := sealCall_eval b
  let answer := decide (d.stacks left = d.stacks right)
  have hc27 : c.stacks 27 = [answer] := by simp [hcs, hb17, hb28, hb27, answer]
  let e := popped 27 answer [] c
  have he := pop_eval 27 c answer [] hc27
  refine ⟨(7 * (d.stacks left).length + 5) +
      ((7 * (a.stacks right).length + 5) + (n + 1)), e, ?_,
    ha.seq (hb.seq (hc.seq he)), ?_, ?_, ?_⟩
  · rw [haRight, hb17, hb28] at *
    omega
  · funext j
    by_cases hj17 : j = 17 <;> by_cases hj28 : j = 28 <;> by_cases hj27 : j = 27 <;>
      simp [e, popped, hcs, b, a, afterCopy, StackRoutines.copyStacks,
        Function.update_apply, hj17, hj28, hj27, h17, h28, h27]
  · simp [e, popped, readRegs, hc6, b, a, afterCopy]
  · simp [e, popped, readRegs, answer]

def cellPorts : Fin 12 ↪ Fin 32 := ⟨![0,11,1,2,10,13,16,17,18,19,20,21], by decide⟩
def cellCall : Code := liftCommand SubexpScalarCellRead.command 0 1 smallRegs cellPorts

theorem cellCall_eval (p N : ℕ) [Fact p.Prime] (T : Fin N → Fin N → ZMod p)
    (row col : Fin N) (d : Data)
    (hT : d.stacks 0 = (BasisTransposeProgram.rows (MatrixWordEncoding.code p) T).flatten)
    (hN : d.stacks 1 = unary N) (hr : d.stacks 2 = unary row.val)
    (hc : d.stacks 10 = unary col.val)
    (hw : d.stacks 13 = unary (2 * MatrixWordEncoding.width p + 1))
    (he : d.stacks 11 = [])
    (clean : ∀ i : Fin 32, 16 ≤ i.val → i.val ≤ 21 → d.stacks i = []) :
    ∃ n e, n ≤ SubexpScalarCellRead.cost N row.val col.val (2 * MatrixWordEncoding.width p + 1) + 1 ∧
      Eval cellCall n d e ∧
      e.stacks = Function.update d.stacks 11 (Encoding.frame (MatrixWordEncoding.word p (T row col))) ∧
      e.regs 6 = d.regs 6 := by
  let a := projectState smallRegs cellPorts d
  obtain ⟨n, b, hb, hn, hbs⟩ := SubexpScalarCellRead.scalar_command_eval p N T row col a
    hT hN hr hc hw he (by
      intro i hi
      fin_cases i <;> norm_num [Fin.coe_ofNat_eq_mod] at hi
      all_goals exact clean _ (by decide) (by decide))
  let e := embedState smallRegs cellPorts d b
  refine ⟨n + 1, e, by omega,
    eval_liftCommand_from_state SubexpScalarCellRead.command 0 1 smallRegs cellPorts d
      smallRegs.injective cellPorts.injective hb, ?_, ?_⟩
  · change Function.extend cellPorts b.stacks d.stacks = _
    rw [hbs, ProgramLinking.extend_update cellPorts.injective]
    have hbase := congrArg StructuredProgram.State.stacks
      (embedState_project smallRegs cellPorts d smallRegs.injective cellPorts.injective)
    change Function.extend cellPorts a.stacks d.stacks = d.stacks at hbase
    rw [hbase]
    rfl
  · exact embedState_register_frame smallRegs cellPorts d b 6 (by
      rintro ⟨i, hi⟩
      exact smallRegs_ne_six i hi)

def known (src : Fin 32) : Code := copy src 11

theorem known_eval (src : Fin 32) (hs : src ≠ 11) (ht : src ≠ 31)
    (d : Data) (he : d.stacks 11 = []) (h31 : d.stacks 31 = []) :
    ∃ e, Eval (known src) (7 * (d.stacks src).length + 5) d e ∧
      e.stacks = Function.update d.stacks 11 (d.stacks src) ∧ e.regs 6 = d.regs 6 := by
  refine ⟨afterCopy d src 11 0 1,
    SubexpScanPrimitives.copy_eval d src 11 31 0 1 hs ht (by decide) (by decide) h31, ?_, ?_⟩
  · simp [afterCopy, StackRoutines.copyStacks, he]
  · simp [afterCopy, readRegs]

def normalize : Code := .seq (.base (.atom (.set 13 false)))
  (.seq (.base (.atom (.set 14 true))) (.base (.atom (.set 15 false))))

def normalized (d : Data) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 13 false) 14 true) 15 false, d.stacks⟩

theorem normalize_eval (d : Data) : Eval normalize 3 d (normalized d) := by
  let a := (StructuredProgram.Atom.set (13 : Fin 16) false).eval d
  let b := (StructuredProgram.Atom.set (14 : Fin 16) true).eval a
  exact (Eval.base (StructuredProgram.Eval.atom (.set 13 false) d)).seq
    ((Eval.base (StructuredProgram.Eval.atom (.set 14 true) a)).seq
      (Eval.base (StructuredProgram.Eval.atom (.set 15 false) b)))

def finish : Code := .seq (transfer 11 12)
  (.seq (clear 8) (.seq (clear 9) (.seq (clear 10) normalize)))

def finished (s : Store) : Store :=
  Function.update (Function.update (Function.update
    (Function.update (Function.update s 11 []) 12 ((s 11).reverse ++ s 12)) 8 []) 9 []) 10 []

theorem finish_eval (d : Data) :
    ∃ e, Eval finish
      (3 * (d.stacks 11).length + 2 * ((d.stacks 8).length + (d.stacks 9).length +
        (d.stacks 10).length) + 15) d e ∧ e.stacks = finished d.stacks ∧
      e.regs 6 = d.regs 6 ∧ e.regs 13 = false ∧ e.regs 14 = true ∧ e.regs 15 = false := by
  let a := afterTransfer d 11 12 0 1
  let b := cleared 8 a
  let c := cleared 9 b
  let f := cleared 10 c
  let e := normalized f
  have h := (SubexpScanPrimitives.transfer_eval d 11 12 0 1 (by decide) (by decide)).seq
    ((clear_eval 8 a).seq ((clear_eval 9 b).seq ((clear_eval 10 c).seq (normalize_eval f))))
  refine ⟨e, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · convert h using 1
    · rfl
    · simp [a, b, c, cleared, afterTransfer, StackRoutines.transferStacks]
      omega
  all_goals simp [e, f, c, b, a, normalized, cleared, afterTransfer, readRegs]

end SubexponentialSAT.Subexp.GlobalBasisEntryCore

end OAI.Algorithms
