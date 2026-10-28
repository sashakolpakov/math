import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramGraphCandidate

namespace OAI.Algorithms

/-! The matrix-record callback has separate parser registers. The physical
candidate verifier cannot overwrite the outer parser's tag/present bits. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open StructuredProgram (Atom)

abbrev GraphOuterState := State 20 40

def graphOuterRegisters : Fin 16 → Fin 20 := Fin.castAdd 4

def graphOuterProject (a : GraphOuterState) : GraphCandidateState :=
  ⟨a.regs ∘ graphOuterRegisters,a.stacks⟩

def GraphOuterReady (D r q : ℕ) (qbits Dbits : List Bool) (a : GraphOuterState) : Prop :=
  GraphCandidateReady D r q qbits Dbits (graphOuterProject a)

abbrev graphOuterCallback : Cmd 20 40 :=
  .seq (.call (ProgramLinking.liftProgram graphCandidateProgram graphOuterRegisters id)) (.base (.atom (.copy 19 15)))

theorem graphOuterCallback_eval {D r q : ℕ} {qbits Dbits : List Bool}
    (Q : Fin D → Cayley.Cube r) (a : GraphOuterState) (ha : GraphOuterReady D r q qbits Dbits a)
    (hq : a.stacks 39 = (matrixFrames Q).reverse) :
    ∃ (n : ℕ) (out : GraphOuterState), n ≤ graphCandidateBudget D r qbits.length Dbits.length + 2 ∧
      Eval graphOuterCallback n a out ∧ GraphOuterReady D r q qbits Dbits out ∧
      out.regs 19 = decide (WalshExistence.Good q Q) ∧
      out.regs 17 = a.regs 17 ∧ out.regs 18 = a.regs 18 ∧
      out.stacks 38 = a.stacks 38 ∧ out.stacks 39 = [] ∧
      out.stacks 29 = matrixFrames Q := by
  obtain ⟨n,small,hn,he,hr,hf,hm,hp,ht⟩ :=
    graphCandidate_eval Q (graphOuterProject a) ha hq
  have hin : embedState graphOuterRegisters id a (graphOuterProject a) = a := by
    apply SubexpScanPrimitives.embedState_eq _ _ (Fin.castAdd_injective _ _)
      Function.injective_id
    · intro i; rfl
    · intro i; rfl
    · intros; rfl
    · intros; rfl
  have hcall := eval_call_lifted graphCandidateProgram graphOuterRegisters id a
    (Fin.castAdd_injective _ _) Function.injective_id (compiled_halt_trace he 39 29)
  rw [hin] at hcall
  let middle := embedState graphOuterRegisters id a small
  let out := (Atom.copy 19 15).eval middle
  have hst : out.stacks = small.stacks := by
    funext i
    change middle.stacks i = small.stacks i
    exact embedState_stack graphOuterRegisters id a small Function.injective_id i
  have hrst : (graphOuterProject out).stacks = small.stacks := hst
  have hflag : out.regs 19 = small.regs 15 := by
    change middle.regs 15 = small.regs 15
    exact embedState_register graphOuterRegisters id a small (Fin.castAdd_injective _ _) 15
  have hreg (i : Fin 20) (hi : 16 ≤ i.val) : middle.regs i = a.regs i := by
    apply embedState_register_frame
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    simp [graphOuterRegisters] at hv
    omega
  refine ⟨n+1+1,out,by omega,hcall.seq (Eval.base (.atom _ middle)),
    GraphCandidateReady.of_stacks_eq hrst hr,?_,?_,?_,?_,?_,?_⟩
  · rw [hflag]
    cases h : small.regs 15 <;> simp_all
  · change middle.regs 17 = a.regs 17
    exact hreg 17 (by decide)
  · change middle.regs 18 = a.regs 18
    exact hreg 18 (by decide)
  · rw [congrFun hst 38]
    exact ht
  · rw [congrFun hst 39]
    exact hp
  · rw [congrFun hst 29]
    exact hm

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
