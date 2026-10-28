import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramCandidate
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCodeSearch

namespace OAI.Algorithms

/-! The matrix-record callback has separate parser registers. The physical
candidate verifier cannot overwrite the outer parser's tag/present bits. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open StructuredProgram (Atom)

abbrev MatrixSearchState := State 20 28

def matrixRegisters : Fin 16 → Fin 20 := Fin.castAdd 4

def matrixProject (a : MatrixSearchState) : CandidateState :=
  ⟨a.regs ∘ matrixRegisters,a.stacks⟩

def MatrixReady (t D d : ℕ) (a : MatrixSearchState) : Prop :=
  CandidateReady t D d (matrixProject a)

abbrev matrixCallback : Cmd 20 28 :=
  .seq (.call (ProgramLinking.liftProgram candidateProgram matrixRegisters id)) (.base (.atom (.copy 19 15)))

theorem matrixCallback_eval {t D d : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (a : MatrixSearchState) (ha : MatrixReady t D d a)
    (hq : a.stacks 27 = (matrixFrames Q).reverse) :
    ∃ (n : ℕ) (out : MatrixSearchState), n ≤ candidateBudget t D d + 2 ∧
      Eval matrixCallback n a out ∧ MatrixReady t D d out ∧
      out.regs 19 = @decide (SparseCode.HasDistance Q d)
        (LocalCode.decidableHasDistance Q d) ∧
      out.regs 17 = a.regs 17 ∧ out.regs 18 = a.regs 18 ∧
      out.stacks 26 = a.stacks 26 ∧ out.stacks 27 = [] ∧
      out.stacks 18 = matrixFrames Q := by
  obtain ⟨n,small,hn,he,hr,hf,hm,hp,ht⟩ :=
    candidate_eval Q (matrixProject a) ha hq
  have hin : embedState matrixRegisters id a (matrixProject a) = a := by
    apply SubexpScanPrimitives.embedState_eq _ _ (Fin.castAdd_injective _ _)
      Function.injective_id
    · intro i; rfl
    · intro i; rfl
    · intros; rfl
    · intros; rfl
  have hcall := eval_call_lifted candidateProgram matrixRegisters id a
    (Fin.castAdd_injective _ _) Function.injective_id (compiled_halt_trace he 27 18)
  rw [hin] at hcall
  let middle := embedState matrixRegisters id a small
  let out := (Atom.copy 19 15).eval middle
  have hst : out.stacks = small.stacks := by
    funext i
    change middle.stacks i = small.stacks i
    exact embedState_stack matrixRegisters id a small Function.injective_id i
  have hrst : (matrixProject out).stacks = small.stacks := hst
  have hflag : out.regs 19 = small.regs 15 := by
    change middle.regs 15 = small.regs 15
    exact embedState_register matrixRegisters id a small (Fin.castAdd_injective _ _) 15
  have hreg (i : Fin 20) (hi : 16 ≤ i.val) : middle.regs i = a.regs i := by
    apply embedState_register_frame
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    simp [matrixRegisters] at hv
    omega
  refine ⟨n+1+1,out,by omega,hcall.seq (Eval.base (.atom _ middle)),
    CandidateReady.of_stacks_eq hrst hr,?_,?_,?_,?_,?_,?_⟩
  · rw [hflag]
    by_cases hP : SparseCode.HasDistance Q d
    · have hs : small.regs 15 = true := hf.mpr hP
      simp [hs, hP]
    · have hs : small.regs 15 = false := by
        cases h : small.regs 15 <;> simp_all
      simp [hs, hP]
  · change middle.regs 17 = a.regs 17
    exact hreg 17 (by decide)
  · change middle.regs 18 = a.regs 18
    exact hreg 18 (by decide)
  · rw [congrFun hst 26]
    exact ht
  · rw [congrFun hst 27]
    exact hp
  · rw [congrFun hst 18]
    exact hm

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
