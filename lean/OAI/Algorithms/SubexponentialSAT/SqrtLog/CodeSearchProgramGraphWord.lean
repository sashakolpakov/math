import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramGraphCounts
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgramNative

namespace OAI.Algorithms

/-! One complete Walsh query, executed by a fixed program. The inputs contain
an actual binary matrix, a binary character, and binary words for q and D.
No integer inequality is an instruction: the final comparison invokes the
count/arithmetic/guard routine with its measured bit trace. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open StructuredProgram (Atom)

abbrev GraphWordState := State 16 29

def graphCountRegisters : Fin 8 → Fin 16 := Fin.castAdd 8
def graphCountStacks : Fin 18 → Fin 29 := Fin.castAdd 11
def graphCheckRegisters : Fin 9 → Fin 16 := Fin.castAdd 7
def graphCheckStacks : Fin 14 → Fin 29 :=
  ![16,17,9,18,19,20,21,22,23,24,25,26,27,28]

theorem graphCheckStacks_injective : Function.Injective graphCheckStacks := by decide

abbrev graphWordCommand : Cmd 16 29 :=
  .seq (liftCommand graphCountsCommand 11 9 graphCountRegisters graphCountStacks) <|
  .seq (.base (.atom (.copy 15 7))) <|
  .seq (liftCommand CodeSearchWalshProgram.command 0 0 graphCheckRegisters graphCheckStacks) <|
  .seq (.base (.atom (.bnot 8 8))) (.base (.atom (.band 15 15 8)))

def graphWordProgram := compiled graphWordCommand 11 9

def graphWordBudget (D r qlen Dlen : ℕ) := graphCountsBudget D r +
  700 * (2 * (qlen + Dlen + D) + 4)^2 + 5

def graphWordRejects {r D : ℕ} (s : Fin D → Cayley.Cube r)
    (a : Cayley.Cube r) (q : ℕ) : Prop :=
  a ≠ 0 ∧ ¬CodeSearchWalshProgram.good q D (WalshExistence.parityWeight s a)

instance {r D : ℕ} (s : Fin D → Cayley.Cube r) (a : Cayley.Cube r) (q : ℕ) :
    Decidable (graphWordRejects s a q) := by unfold graphWordRejects; infer_instance

theorem parityWeight_le {r D : ℕ} (s : Fin D → Cayley.Cube r) (a : Cayley.Cube r) :
    WalshExistence.parityWeight s a ≤ D := by
  unfold WalshExistence.parityWeight
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- All helper scratch stacks are restored, and the two binary scalar sources
are preserved. The designated Boolean result means this character rejects
this candidate graph. -/
theorem graphWord_eval {r D : ℕ} (s : Fin D → Cayley.Cube r)
    (x : Cayley.Cube r) (q : ℕ) (qbits Dbits : List Bool)
    (hq : BinaryArithmetic.toNat qbits = q) (hD : BinaryArithmetic.toNat Dbits = D)
    (a : GraphWordState)
    (hin : projectState graphCountRegisters graphCountStacks a =
      extendPairState (matrixInput s x (a.regs ∘ graphCountRegisters)) qbits Dbits)
    (hclean : ∀ i : Fin 29, 18 ≤ i.val → a.stacks i = []) :
    ∃ (n : ℕ) (out : GraphWordState), n + 1 ≤ graphWordBudget D r qbits.length Dbits.length ∧
      Eval graphWordCommand n a out ∧ out.regs 15 = decide (graphWordRejects s x q) ∧
      out.stacks 16 = qbits ∧ out.stacks 17 = Dbits ∧
      (∀ i : Fin 29, 18 ≤ i.val → out.stacks i = []) ∧
      out.regs 13 = a.regs 13 ∧ out.regs 14 = a.regs 14 := by
  obtain ⟨nc,c,hnc,hec,hcn,hch,hcq,hcD⟩ :=
    graphCounts_eval s x (a.regs ∘ graphCountRegisters) qbits Dbits
  rw [← hin] at hec
  let b := embedState graphCountRegisters graphCountStacks a c
  have hb := eval_liftCommand_from_state graphCountsCommand 11 9
    graphCountRegisters graphCountStacks a (Fin.castAdd_injective _ _)
      (Fin.castAdd_injective _ _) hec
  have hbreg (i : Fin 16) (hi : 8 ≤ i.val) : b.regs i = a.regs i := by
    apply embedState_register_frame
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    simp [graphCountRegisters] at hv
    omega
  have hbstack (i : Fin 29) (hi : 18 ≤ i.val) : b.stacks i = a.stacks i := by
    apply embedState_stack_frame
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    simp [graphCountStacks] at hv
    omega
  have hbq : b.stacks 16 = qbits :=
    (embedState_stack graphCountRegisters graphCountStacks a c
      (Fin.castAdd_injective _ _) 16).trans hcq
  have hbD : b.stacks 17 = Dbits :=
    (embedState_stack graphCountRegisters graphCountStacks a c
      (Fin.castAdd_injective _ _) 17).trans hcD
  have hbh : b.stacks 9 = List.replicate (WalshExistence.parityWeight s x) true :=
    (embedState_stack graphCountRegisters graphCountStacks a c
      (Fin.castAdd_injective _ _) 9).trans hch
  have hbn : b.regs 7 = decide (x ≠ 0) :=
    (embedState_register graphCountRegisters graphCountStacks a c
      (Fin.castAdd_injective _ _) 7).trans hcn
  let flagged := (Atom.copy 15 7).eval b
  have hfclean (j : Fin 14) (hj : 3 ≤ j.val) :
      flagged.stacks (graphCheckStacks j) = [] := by
    change b.stacks (graphCheckStacks j) = []
    have hidx : 18 ≤ (graphCheckStacks j).val := by
      revert hj
      fin_cases j <;> decide
    exact (hbstack _ hidx).trans (hclean _ hidx)
  obtain ⟨nh,hnh,e,he,hef,hes,her⟩ := CodeSearchWalshProgram.command_lifted
    graphCheckRegisters graphCheckStacks (Fin.castAdd_injective _ _)
      graphCheckStacks_injective flagged hfclean
  have hsize : CodeSearchWalshProgram.size
      (projectState graphCheckRegisters graphCheckStacks flagged) =
        qbits.length + Dbits.length + WalshExistence.parityWeight s x := by
    simp [CodeSearchWalshProgram.size,CodeSearchWalshProgram.inputLength,projectState,graphCheckStacks,
      flagged,Atom.eval,Atom.instr,execInstr,StructuredProgram.State.ofCfg,hbq,hbD,hbh]
  have hpass : e.regs 8 = decide (CodeSearchWalshProgram.good q D
      (WalshExistence.parityWeight s x)) := by
    simpa [CodeSearchWalshProgram.pass,projectState,graphCheckRegisters,graphCheckStacks,
      flagged,Atom.eval,Atom.instr,execInstr,StructuredProgram.State.ofCfg,
      StructuredProgram.State.withPC,hbq,hbD,hbh,hq,hD] using hef
  have her15 : e.regs 15 = decide (x ≠ 0) := by
    rw [her 15 (by
      rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      simp [graphCheckRegisters] at hv
      omega)]
    exact hbn
  let negated := (Atom.bnot 8 8).eval e
  let out := (Atom.band 15 15 8).eval negated
  have houtst : out.stacks = b.stacks := hes
  have houtreg (i : Fin 16) (hi8 : i ≠ 8) (hi15 : i ≠ 15) (hi9 : 9 ≤ i.val) :
      out.regs i = a.regs i := by
    have hri : e.regs i = flagged.regs i := her i (by
      rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      simp [graphCheckRegisters] at hv
      omega)
    simp [out,negated,flagged,Atom.eval,Atom.instr,execInstr,
      StructuredProgram.State.ofCfg,hi8,hi15,hri,
      hbreg i (by omega)]
  refine ⟨nc+1+(1+(nh+(1+1))),out,?_,
    hb.seq ((Eval.base (.atom _ b)).seq (he.seq
      ((Eval.base (.atom _ e)).seq (Eval.base (.atom _ negated))))),?_,?_,?_,?_,?_,?_⟩
  · rw [hsize] at hnh
    have hp := parityWeight_le s x
    have hsquare : (2 * (qbits.length + Dbits.length + WalshExistence.parityWeight s x) + 4)^2 ≤
        (2 * (qbits.length + Dbits.length + D) + 4)^2 := Nat.pow_le_pow_left (by omega) 2
    unfold graphWordBudget
    omega
  · simp [out,negated,Atom.eval,Atom.instr,execInstr,
      StructuredProgram.State.ofCfg,hpass,her15,graphWordRejects]
    apply Bool.eq_iff_iff.mpr
    simp
    by_cases h : x ≠ 0 ∧ ¬ CodeSearchWalshProgram.good q D
        (WalshExistence.parityWeight s x)
    · simp [h]
    · simp [h]
  · rw [congrFun houtst 16]; exact hbq
  · rw [congrFun houtst 17]; exact hbD
  · intro i hi
    rw [congrFun houtst i,hbstack i hi]
    exact hclean i hi
  · exact houtreg 13 (by decide) (by decide) (by decide)
  · exact houtreg 14 (by decide) (by decide) (by decide)

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
