import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramLocalExistence
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramGenerateFrame

namespace OAI.Algorithms

/-! Closed local-code search, starting with unary numerical metadata. Both
finite lists are actually generated before the paid first-success search. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open StructuredProgram (Atom)

abbrev LocalProgramState := State 20 32

def localGenerateRegisters : Fin 16 → Fin 20 := Fin.castAdd 4

def localWordsPorts : Fin 12 → Fin 32 := ![0,1,2,3,4,5,6,7,8,28,24,25]
def localMatricesPorts : Fin 12 → Fin 32 := ![0,1,2,3,4,5,6,7,8,29,26,25]
def localSearchStacks : Fin 28 → Fin 32 := Fin.castAdd 4

abbrev localProgramCommand : Cmd 20 32 :=
  .seq (liftCommand (generateCommand 3) 9 10 localGenerateRegisters localWordsPorts) <|
  .seq (liftCommand (generateCommand 3) 9 10 localGenerateRegisters localMatricesPorts) <|
  .seq (.base (.atom (.set 19 false)))
    (.call (ProgramLinking.liftProgram matrixSearchProgram id localSearchStacks))

def localProgram := compiled localProgramCommand 28 18

def localProgramBudget (t D d : ℕ) :=
  generateBudget 3 D + generateBudget 3 (t * D) + matrixSearchBudget t D d + 2

structure LocalProgramReady (t D d : ℕ) (a : LocalProgramState) : Prop where
  work : ∀ i : Fin 28, i ≠ 19 → i ≠ 20 → a.stacks (localSearchStacks i) = []
  rows : a.stacks 19 = List.replicate t true
  distance : a.stacks 20 = List.replicate d true
  dimension : a.stacks 28 = List.replicate D true
  entries : a.stacks 29 = List.replicate (t * D) true

private theorem localEmpty {t D d : ℕ} {a : LocalProgramState} (ha : LocalProgramReady t D d a)
    (i : Fin 32) (hi : i.val < 28) (h19 : i ≠ 19) (h20 : i ≠ 20) : a.stacks i = [] := by
  let j : Fin 28 := ⟨i.val,hi⟩
  have hj : localSearchStacks j = i := Fin.ext rfl
  rw [← hj]
  apply ha.work j
  · intro h; apply h19; rw [← hj,h]; rfl
  · intro h; apply h20; rw [← hj,h]; rfl

theorem localProgram_runsIn {t D d : ℕ} (a : LocalProgramState)
    (ha : LocalProgramReady t D d a)
    (hex : ∃ Q : Fin t → Fin D → SparseCode.F3, SparseCode.HasDistance Q d) :
    ∃ (out : LocalProgramState) (Q : Fin t → Fin D → SparseCode.F3),
      SparseCode.HasDistance Q d ∧ out.stacks 18 = matrixFrames Q ∧
      RunsIn localProgram (localProgramBudget t D d)
        (a.withPC (some localProgram.entry)) (out.withPC none) := by
  have hgw : GenerateReady (projectState localGenerateRegisters localWordsPorts a) := by
    refine ⟨?_,?_,?_⟩
    · intro i; fin_cases i <;>
        apply localEmpty ha <;> decide
    · exact localEmpty ha 24 (by decide) (by decide) (by decide)
    · exact localEmpty ha 25 (by decide) (by decide) (by decide)
  obtain ⟨nw,b,hnw,hew,hbs,_⟩ := generate_lifted_update 3 localGenerateRegisters localWordsPorts
    (Fin.castAdd_injective _ _) (by decide) a hgw
  have hbs' : b.stacks = Function.update a.stacks 24
      (ProgramEncoding.encodeRecords (framedCandidates 3 D)) := by
    simpa [localWordsPorts,ha.dimension] using hbs
  have hbframe (j : Fin 32) (hj : j ≠ 24) : b.stacks j = a.stacks j := by
    rw [hbs',Function.update_of_ne hj]
  have hgm : GenerateReady (projectState localGenerateRegisters localMatricesPorts b) := by
    refine ⟨?_,?_,?_⟩
    · intro i; fin_cases i <;>
        apply Eq.trans (hbframe _ (by decide)) <;>
        apply localEmpty ha <;> decide
    · change b.stacks 26 = []
      rw [hbs']; simp only [Function.update_of_ne (by decide : (26 : Fin 32) ≠ 24)]
      exact localEmpty ha 26 (by decide) (by decide) (by decide)
    · change b.stacks 25 = []
      rw [hbs']; simp only [Function.update_of_ne (by decide : (25 : Fin 32) ≠ 24)]
      exact localEmpty ha 25 (by decide) (by decide) (by decide)
  obtain ⟨nm,c,hnm,hem,hcs,_⟩ := generate_lifted_update 3 localGenerateRegisters localMatricesPorts
    (Fin.castAdd_injective _ _) (by decide) b hgm
  have hb29 : b.stacks 29 = List.replicate (t * D) true := by
    rw [hbs']; exact ha.entries
  have hcs' : c.stacks = Function.update b.stacks 26
      (ProgramEncoding.encodeRecords (framedCandidates 3 (t * D))) := by
    simpa [localMatricesPorts,hb29] using hcs
  let flagged := (Atom.set 19 false).eval c
  let base := projectState id localSearchStacks flagged
  have hwork (i : Fin 28) (h19 : i ≠ 19) (h20 : i ≠ 20) (h24 : i ≠ 24) (h26 : i ≠ 26) :
      base.stacks i = [] := by
    change c.stacks (localSearchStacks i) = []
    rw [hcs',hbs']
    have h24' : localSearchStacks i ≠ 24 := by
      intro h; apply h24; exact Fin.ext (by simpa [localSearchStacks] using congrArg Fin.val h)
    have h26' : localSearchStacks i ≠ 26 := by
      intro h; apply h26; exact Fin.ext (by simpa [localSearchStacks] using congrArg Fin.val h)
    simp only [Function.update_of_ne h24',Function.update_of_ne h26']
    exact ha.work i h19 h20
  have hready : MatrixReady t D d base := by
    constructor
    · intro i
      apply hwork <;> intro h <;> have hv := congrArg Fin.val h <;> simp only at hv <;> omega
    · change c.stacks 19 = _; rw [hcs',hbs']; exact ha.rows
    · change c.stacks 20 = _; rw [hcs',hbs']; exact ha.distance
    · exact hwork 21 (by decide) (by decide) (by decide) (by decide)
    · exact hwork 22 (by decide) (by decide) (by decide) (by decide)
    · exact hwork 23 (by decide) (by decide) (by decide) (by decide)
    · change c.stacks 24 = _; rw [hcs',hbs']; rfl
    · exact hwork 25 (by decide) (by decide) (by decide) (by decide)
    · have h := hwork 18 (by decide) (by decide) (by decide) (by decide)
      change (base.stacks 18).length ≤ _
      rw [h]; exact Nat.zero_le _
  have hinv : MatrixInvariant t D d base := by
    refine ⟨hready,?_⟩
    simp [base,flagged,projectState,Atom.eval,Atom.instr,execInstr,
      StructuredProgram.State.ofCfg]
  obtain ⟨out,tail,Q,hQ,hout,ns,hns,hs⟩ := matrix_search_runsIn base hinv hex
    (base.regs 17) (base.regs 18) (base.regs 19)
  have hsource : base.stacks 26 = ProgramEncoding.encodeRecords (framedCandidates 3 (t * D)) := by
    change c.stacks 26 = _; rw [hcs']; rfl
  have hentry : RecordPrograms.state matrixPorts base (base.regs 17) (base.regs 18)
      (base.regs 19) (ProgramEncoding.encodeRecords (framedCandidates 3 (t * D))) [] = base :=
    RecordPrograms.state_eq_self _ _ _ _ _ _ _ rfl rfl rfl hsource
      (hwork 27 (by decide) (by decide) (by decide) (by decide))
  rw [hentry] at hs
  let small := RecordPrograms.state matrixPorts out false true true tail []
  let final := embedState id localSearchStacks flagged small
  have hcall := eval_call_from_state matrixSearchProgram id localSearchStacks flagged
    Function.injective_id (Fin.castAdd_injective _ _) hs
  have hfinal : final.stacks 18 = matrixFrames Q := by
    have h := embedState_stack id localSearchStacks flagged small (Fin.castAdd_injective _ _) 18
    exact h.trans (by simpa [small,RecordPrograms.state,matrixPorts] using hout)
  refine ⟨final,Q,hQ,hfinal,nw+(nm+(1+ns))+1,?_,?_⟩
  · have hlenw : (a.stacks (localWordsPorts 9)).length = D := by simp [localWordsPorts,ha.dimension]
    have hlenm : (b.stacks (localMatricesPorts 9)).length = t * D := by simp [localMatricesPorts,hb29]
    rw [hlenw] at hnw
    rw [hlenm] at hnm
    unfold localProgramBudget
    omega
  · exact compiled_halt_trace (hew.seq (hem.seq ((Eval.base (.atom _ c)).seq hcall))) 28 18

/-- Unconditional success under the explicit arithmetic range proved by the
code-parameter constructor. No local-code existence oracle is a premise. -/
theorem localProgram_distance (D B ell t : ℕ) (hB : 0 < B) (hell : 0 < ell)
    (hD : D ≤ 2 ^ ell) (ht : D ≤ 8 * B * t) (a : LocalProgramState)
    (ha : LocalProgramReady t D (D / (100 * B * ell) + 1) a) :
    ∃ (out : LocalProgramState) (Q : Fin t → Fin D → SparseCode.F3),
      SparseCode.HasDistance Q (D / (100 * B * ell) + 1) ∧ out.stacks 18 = matrixFrames Q ∧
      RunsIn localProgram (localProgramBudget t D (D / (100 * B * ell) + 1))
        (a.withPC (some localProgram.entry)) (out.withPC none) := by
  apply localProgram_runsIn a ha
  exact ⟨LocalCode.localMatrix D B ell t,LocalCode.localMatrix_distance D B ell t hB hell hD ht⟩

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
