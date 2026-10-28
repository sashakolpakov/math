import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BinaryPrograms
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-!
# Source-preserving arithmetic calls on fixed Boolean-stack ports

Operands are copied into distinct work ports before the actual finite adder or
multiplier runs. The source ports may coincide. The only final stack change is
the output word; every work port is restored to its incoming empty state.
-/

namespace SubexponentialSAT.ArithmeticCalls

open BitProgram StructuredCalls

structure Ports (S : ℕ) where
  left : Fin S
  right : Fin S
  out : Fin S
  work : Fin 5 ↪ Fin S
  out_ne_left : out ≠ left
  out_ne_right : out ≠ right
  work_ne_left : ∀ i, work i ≠ left
  work_ne_right : ∀ i, work i ≠ right
  work_ne_out : ∀ i, work i ≠ out

abbrev Data (S : ℕ) := StructuredProgram.State 8 S

def Valid {S : ℕ} (p : Ports S) (d : Data S) : Prop :=
  d.stacks p.out = [] ∧ ∀ i, d.stacks (p.work i) = []

@[simp] theorem left_ne_work {S : ℕ} (p : Ports S) (i : Fin 5) :
    p.left ≠ p.work i := (p.work_ne_left i).symm
@[simp] theorem right_ne_work {S : ℕ} (p : Ports S) (i : Fin 5) :
    p.right ≠ p.work i := (p.work_ne_right i).symm
@[simp] theorem out_ne_work {S : ℕ} (p : Ports S) (i : Fin 5) :
    p.out ≠ p.work i := (p.work_ne_out i).symm

abbrev copyAt {S : ℕ} (source target scratch : Fin S) : Cmd 8 S :=
  .call (StackRoutines.copyProgram source target scratch 0 1)

def afterCopy {S : ℕ} (source target : Fin S) (d : Data S) : Data S :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks target (d.stacks source)⟩

theorem copyAt_eval {S : ℕ} (source target scratch : Fin S) (d : Data S)
    (hst : source ≠ target) (hss : source ≠ scratch) (hts : scratch ≠ target)
    (ht : d.stacks target = []) (hs : d.stacks scratch = []) :
    Eval (copyAt source target scratch) (7 * (d.stacks source).length + 5)
      d (afterCopy source target d) := by
  have h := ListRegisterProgram.copy_run source target scratch (0 : Fin 8) 1
    hst hss hts (by decide) d.regs d.stacks hs
  apply Eval.call
  simpa [afterCopy, ListRegisterProgram.Run, StructuredProgram.State.withPC,
    StackRoutines.copyStacks, ht] using h

def mulPorts {S : ℕ} (p : Ports S) : Fin 6 → Fin S :=
  ![p.work 0, p.work 1, p.out, p.work 2, p.work 3, p.work 4]

def addPorts {S : ℕ} (p : Ports S) : Fin 3 → Fin S :=
  ![p.out, p.work 1, p.work 2]

theorem mulPorts_injective {S : ℕ} (p : Ports S) : Function.Injective (mulPorts p) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [mulPorts, p.work.injective.eq_iff, p.work_ne_out]

theorem addPorts_injective {S : ℕ} (p : Ports S) : Function.Injective (addPorts p) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [addPorts, p.work.injective.eq_iff, p.work_ne_out]

abbrev multiplyRaw {S : ℕ} (p : Ports S) : Cmd 8 S :=
  .call (ProgramLinking.liftProgram BinaryPrograms.Mul.program id (mulPorts p))

abbrev addRaw {S : ℕ} (p : Ports S) : Cmd 8 S :=
  .call (ProgramLinking.liftProgram BinaryPrograms.Add.littleEndianProgram id (addPorts p))

abbrev multiplyAt {S : ℕ} (p : Ports S) : Cmd 8 S :=
  .seq (copyAt p.left (p.work 0) (p.work 3))
    (.seq (copyAt p.right (p.work 1) (p.work 3)) (multiplyRaw p))

abbrev addAt {S : ℕ} (p : Ports S) : Cmd 8 S :=
  .seq (copyAt p.left p.out (p.work 3))
    (.seq (copyAt p.right (p.work 1) (p.work 3))
      (.seq (.base (.atom (.set 0 false))) (addRaw p)))

def mulReady {S : ℕ} (p : Ports S) (d : Data S) : Data S :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks (p.work 0) (d.stacks p.left))
      (p.work 1) (d.stacks p.right)⟩

def addReady {S : ℕ} (p : Ports S) (d : Data S) : Data S :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks p.out (d.stacks p.left))
      (p.work 1) (d.stacks p.right)⟩

private theorem copy_mul_ready {S : ℕ} (p : Ports S) (d : Data S) :
    afterCopy p.right (p.work 1) (afterCopy p.left (p.work 0) d) = mulReady p d := by
  simp [afterCopy, mulReady, StackRoutines.readRegs_reset]

private theorem copy_add_ready {S : ℕ} (p : Ports S) (d : Data S) :
    afterCopy p.right (p.work 1) (afterCopy p.left p.out d) = addReady p d := by
  simp [afterCopy, addReady, StackRoutines.readRegs_reset, p.out_ne_right.symm]

private theorem embed_mul_start {S : ℕ} (p : Ports S) (d : Data S) (hv : Valid p d) :
    embedState id (mulPorts p) d
      ⟨(mulReady p d).regs,
        BinaryPrograms.Mul.stackState (d.stacks p.left) (d.stacks p.right) [] [] [] []⟩ =
      mulReady p d := by
  apply embedState_eq_of_ports id (mulPorts p) d _ _ Function.injective_id (mulPorts_injective p)
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> simp [mulReady, mulPorts, BinaryPrograms.Mul.stackState,
      p.work.injective.eq_iff, hv.1, hv.2]
  · intro i hi
    have h0 : i ≠ p.work 0 := fun h => hi ⟨0, h.symm⟩
    have h1 : i ≠ p.work 1 := fun h => hi ⟨1, h.symm⟩
    simp [mulReady, h0, h1]

private theorem embed_mul_finish {S : ℕ} (p : Ports S) (d : Data S) (hv : Valid p d)
    (rf : Fin 8 → Bool) (word : List Bool) :
    embedState id (mulPorts p) d
      ⟨rf, BinaryPrograms.Mul.stackState [] [] word [] [] []⟩ =
      (⟨rf, Function.update d.stacks p.out word⟩ : Data S) := by
  apply embedState_eq_of_ports id (mulPorts p) d _ _ Function.injective_id (mulPorts_injective p)
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> simp [mulPorts, BinaryPrograms.Mul.stackState, p.work_ne_out, hv.2]
  · intro i hi
    have ho : i ≠ p.out := fun h => hi ⟨2, h.symm⟩
    simp [ho]

private theorem embed_add_start {S : ℕ} (p : Ports S) (d : Data S) (hv : Valid p d) :
    embedState id (addPorts p) d
      ⟨(addReady p d).regs,
        BinaryPrograms.Add.stackState (d.stacks p.left) (d.stacks p.right) []⟩ =
      addReady p d := by
  apply embedState_eq_of_ports id (addPorts p) d _ _ Function.injective_id (addPorts_injective p)
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> simp [addReady, addPorts, BinaryPrograms.Add.stackState,
      p.work.injective.eq_iff, p.work_ne_out, hv.2]
  · intro i hi
    have ho : i ≠ p.out := fun h => hi ⟨0, h.symm⟩
    have h1 : i ≠ p.work 1 := fun h => hi ⟨1, h.symm⟩
    simp [addReady, ho, h1]

private theorem embed_add_finish {S : ℕ} (p : Ports S) (d : Data S) (hv : Valid p d)
    (rf : Fin 8 → Bool) (word : List Bool) :
    embedState id (addPorts p) d
      ⟨rf, BinaryPrograms.Add.stackState word [] []⟩ =
      (⟨rf, Function.update d.stacks p.out word⟩ : Data S) := by
  apply embedState_eq_of_ports id (addPorts p) d _ _ Function.injective_id (addPorts_injective p)
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> simp [addPorts, BinaryPrograms.Add.stackState, p.work_ne_out, hv.2]
  · intro i hi
    have ho : i ≠ p.out := fun h => hi ⟨0, h.symm⟩
    simp [ho]

/-- Source-preserving binary multiplication by an actual finite program.
All five work stacks are empty in the returned state, because only out changes. -/
theorem multiplyAt_eval {S : ℕ} (p : Ports S) (d : Data S) (hv : Valid p d) :
    ∃ (t : ℕ) (rf : Fin 8 → Bool) (word : List Bool),
      Eval (multiplyAt p) t d ⟨rf, Function.update d.stacks p.out word⟩ ∧
      BinaryArithmetic.toNat word =
        BinaryArithmetic.toNat (d.stacks p.left) * BinaryArithmetic.toNat (d.stacks p.right) ∧
      word.length ≤ (d.stacks p.left).length + (d.stacks p.right).length + 1 ∧
      t ≤ 100 * ((d.stacks p.left).length + (d.stacks p.right).length + 1) ^ 2 := by
  let first := afterCopy p.left (p.work 0) d
  have hleft := copyAt_eval p.left (p.work 0) (p.work 3) d
    (left_ne_work p 0) (left_ne_work p 3)
    (by simp [p.work.injective.eq_iff]) (hv.2 0) (hv.2 3)
  have hrightWord : first.stacks p.right = d.stacks p.right := by
    simp [first, afterCopy]
  have hright := copyAt_eval p.right (p.work 1) (p.work 3) first
    (right_ne_work p 1) (right_ne_work p 3)
    (by simp [p.work.injective.eq_iff])
    (by simp [first, afterCopy, p.work.injective.eq_iff, hv.2])
    (by simp [first, afterCopy, p.work.injective.eq_iff, hv.2])
  rw [hrightWord] at hright
  change Eval _ _ first
    (afterCopy p.right (p.work 1) (afterCopy p.left (p.work 0) d)) at hright
  rw [copy_mul_ready] at hright
  let word := BinaryPrograms.Mul.accumulate (d.stacks p.left) (d.stacks p.right) []
  obtain ⟨rf, t, htime, htrace⟩ := BinaryPrograms.Mul.run (mulReady p d).regs
    (d.stacks p.left) (d.stacks p.right) [] (d.stacks p.right).length le_rfl (by simp)
  have hcall := eval_call_lifted BinaryPrograms.Mul.program id (mulPorts p) d
    Function.injective_id (mulPorts_injective p)
    (a := ⟨(mulReady p d).regs,
      BinaryPrograms.Mul.stackState (d.stacks p.left) (d.stacks p.right) [] [] [] []⟩)
    (b := ⟨rf, BinaryPrograms.Mul.stackState [] [] word [] [] []⟩) htrace
  rw [embed_mul_start p d hv, embed_mul_finish p d hv] at hcall
  refine ⟨(7 * (d.stacks p.left).length + 5) +
      ((7 * (d.stacks p.right).length + 5) + t), rf, word,
    hleft.seq (hright.seq hcall), ?_, ?_, ?_⟩
  · simpa [word] using BinaryPrograms.Mul.accumulate_value
      (d.stacks p.left) (d.stacks p.right) []
  · have hlen := BinaryPrograms.Mul.accumulate_length
      (d.stacks p.left) (d.stacks p.right) []
    simp only [List.length_nil, Nat.zero_max] at hlen
    dsimp [word]
    omega
  · nlinarith

/-- Source-preserving binary addition, with an explicit carry reset before
the verified little-endian adder. -/
theorem addAt_eval {S : ℕ} (p : Ports S) (d : Data S) (hv : Valid p d) :
    ∃ (t : ℕ) (rf : Fin 8 → Bool) (word : List Bool),
      Eval (addAt p) t d ⟨rf, Function.update d.stacks p.out word⟩ ∧
      BinaryArithmetic.toNat word =
        BinaryArithmetic.toNat (d.stacks p.left) + BinaryArithmetic.toNat (d.stacks p.right) ∧
      word.length ≤ (d.stacks p.left).length + (d.stacks p.right).length + 1 ∧
      t ≤ 100 * ((d.stacks p.left).length + (d.stacks p.right).length + 1) ^ 2 := by
  let first := afterCopy p.left p.out d
  have hleft := copyAt_eval p.left p.out (p.work 3) d
    p.out_ne_left.symm (left_ne_work p 3) (p.work_ne_out 3) hv.1 (hv.2 3)
  have hrightWord : first.stacks p.right = d.stacks p.right := by
    simp [first, afterCopy, p.out_ne_right.symm]
  have hright := copyAt_eval p.right (p.work 1) (p.work 3) first
    (right_ne_work p 1) (right_ne_work p 3)
    (by simp [p.work.injective.eq_iff])
    (by simp [first, afterCopy, p.work_ne_out, hv.2])
    (by simp [first, afterCopy, p.work_ne_out, hv.2])
  rw [hrightWord] at hright
  change Eval _ _ first
    (afterCopy p.right (p.work 1) (afterCopy p.left p.out d)) at hright
  rw [copy_add_ready] at hright
  have hcarry : Eval (.base (.atom (.set 0 false))) 1 (addReady p d) (addReady p d) := by
    have he : (StructuredProgram.Atom.set 0 false).eval (addReady p d) = addReady p d := by
      simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr,
        addReady, readRegs ]
    simpa only [he] using Eval.base
      (StructuredProgram.Eval.atom (StructuredProgram.Atom.set 0 false) (addReady p d))
  let word := BinaryArithmetic.add (d.stacks p.left) (d.stacks p.right)
  obtain ⟨rf, t, htime, htrace⟩ := BinaryPrograms.Add.littleEndian_run (addReady p d).regs
    (d.stacks p.left) (d.stacks p.right)
  have hw : BinaryArithmetic.addCarry ((addReady p d).regs 0)
      (d.stacks p.left) (d.stacks p.right) = word := by
    simp [addReady, readRegs, word, BinaryArithmetic.add]
  rw [hw] at htrace
  have hcall := eval_call_lifted BinaryPrograms.Add.littleEndianProgram id (addPorts p) d
    Function.injective_id (addPorts_injective p)
    (a := ⟨(addReady p d).regs,
      BinaryPrograms.Add.stackState (d.stacks p.left) (d.stacks p.right) []⟩)
    (b := ⟨rf, BinaryPrograms.Add.stackState word [] []⟩) htrace
  rw [embed_add_start p d hv, embed_add_finish p d hv] at hcall
  refine ⟨(7 * (d.stacks p.left).length + 5) +
      ((7 * (d.stacks p.right).length + 5) + (1 + t)), rf, word,
    hleft.seq (hright.seq (hcarry.seq hcall)), BinaryArithmetic.toNat_add _ _, ?_, ?_⟩
  · have hlen := BinaryArithmetic.length_add (d.stacks p.left) (d.stacks p.right)
    dsimp [word]
    have hm : max (d.stacks p.left).length (d.stacks p.right).length ≤
        (d.stacks p.left).length + (d.stacks p.right).length := by omega
    omega
  · have hm : max (d.stacks p.left).length (d.stacks p.right).length ≤
        (d.stacks p.left).length + (d.stacks p.right).length := by omega
    nlinarith

theorem addAt_spec {S : ℕ} (p : Ports S) (d : Data S) (hv : Valid p d) :
    ∃ (t : ℕ) (rf : Fin 8 → Bool) (word : List Bool),
      Eval (addAt p) t d ⟨rf, Function.update d.stacks p.out word⟩ ∧
      BinaryArithmetic.toNat word =
        BinaryArithmetic.toNat (d.stacks p.left) + BinaryArithmetic.toNat (d.stacks p.right) ∧
      word.length ≤ (d.stacks p.left).length + (d.stacks p.right).length + 1 ∧
      t ≤ 100 * ((d.stacks p.left).length + (d.stacks p.right).length + 1) ^ 2 :=
  addAt_eval p d hv

theorem multiplyAt_spec {S : ℕ} (p : Ports S) (d : Data S) (hv : Valid p d) :
    ∃ (t : ℕ) (rf : Fin 8 → Bool) (word : List Bool),
      Eval (multiplyAt p) t d ⟨rf, Function.update d.stacks p.out word⟩ ∧
      BinaryArithmetic.toNat word =
        BinaryArithmetic.toNat (d.stacks p.left) * BinaryArithmetic.toNat (d.stacks p.right) ∧
      word.length ≤ (d.stacks p.left).length + (d.stacks p.right).length + 1 ∧
      t ≤ 100 * ((d.stacks p.left).length + (d.stacks p.right).length + 1) ^ 2 :=
  multiplyAt_eval p d hv

end SubexponentialSAT.ArithmeticCalls

end OAI.Algorithms
