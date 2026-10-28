import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramGraphSearch
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramGenerateFrame

namespace OAI.Algorithms

/-! A closed Walsh graph search: generate both finite lists and search them
using the complete bit verifier. All numerical dimensions are tape data. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open StructuredProgram (Atom)

abbrev GraphProgramState := State 20 44

def graphGenerateRegisters : Fin 16 → Fin 20 := Fin.castAdd 4
def graphCharactersPorts : Fin 12 → Fin 44 := ![0,1,2,3,4,5,6,7,8,40,36,37]
def graphTuplesPorts : Fin 12 → Fin 44 := ![0,1,2,3,4,5,6,7,8,41,38,37]
def graphSearchStacks : Fin 40 → Fin 44 := Fin.castAdd 4

abbrev graphProgramCommand : Cmd 20 44 :=
  .seq (liftCommand (generateCommand 2) 9 10 graphGenerateRegisters graphCharactersPorts) <|
  .seq (liftCommand (generateCommand 2) 9 10 graphGenerateRegisters graphTuplesPorts) <|
  .seq (.base (.atom (.set 19 false)))
    (.call (ProgramLinking.liftProgram graphSearchProgram id graphSearchStacks))

def graphProgram := compiled graphProgramCommand 40 29

def graphProgramBudget (D r qlen Dlen : ℕ) :=
  generateBudget 2 r + generateBudget 2 (D * r) + graphSearchBudget D r qlen Dlen + 2

structure GraphProgramReady (D r q : ℕ) (qbits Dbits : List Bool) (a : GraphProgramState) : Prop where
  work : ∀ i : Fin 40, i ≠ 30 → i ≠ 31 → i ≠ 32 → a.stacks (graphSearchStacks i) = []
  rows : a.stacks 30 = List.replicate D true
  qword : a.stacks 31 = qbits
  Dword : a.stacks 32 = Dbits
  dimension : a.stacks 40 = List.replicate r true
  entries : a.stacks 41 = List.replicate (D * r) true
  qvalue : BinaryArithmetic.toNat qbits = q
  Dvalue : BinaryArithmetic.toNat Dbits = D

private theorem graphEmpty {D r q : ℕ} {qbits Dbits : List Bool} {a : GraphProgramState}
    (ha : GraphProgramReady D r q qbits Dbits a) (i : Fin 44) (hi : i.val < 40)
    (h30 : i ≠ 30) (h31 : i ≠ 31) (h32 : i ≠ 32) : a.stacks i = [] := by
  let j : Fin 40 := ⟨i.val,hi⟩
  have hj : graphSearchStacks j = i := Fin.ext rfl
  rw [← hj]
  apply ha.work j
  · intro h; apply h30; rw [← hj,h]; rfl
  · intro h; apply h31; rw [← hj,h]; rfl
  · intro h; apply h32; rw [← hj,h]; rfl

theorem graphProgram_runsIn {D r q : ℕ} {qbits Dbits : List Bool} (a : GraphProgramState)
    (ha : GraphProgramReady D r q qbits Dbits a)
    (hq : 1 ≤ q) (hsize : r = 0 ∨ 8 * q ^ 2 * (r + 1) ≤ D) :
    ∃ (out : GraphProgramState) (s : Fin D → Cayley.Cube r), WalshExistence.Good q s ∧
      out.stacks 29 = matrixFrames s ∧ RunsIn graphProgram
        (graphProgramBudget D r qbits.length Dbits.length)
        (a.withPC (some graphProgram.entry)) (out.withPC none) := by
  have hgc : GenerateReady (projectState graphGenerateRegisters graphCharactersPorts a) := by
    refine ⟨?_,?_,?_⟩
    · intro i; fin_cases i <;> apply graphEmpty ha <;> decide
    · exact graphEmpty ha 36 (by decide) (by decide) (by decide) (by decide)
    · exact graphEmpty ha 37 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨nc,b,hnc,hec,hbs,_⟩ := generate_lifted_update 2 graphGenerateRegisters graphCharactersPorts
    (Fin.castAdd_injective _ _) (by decide) a hgc
  have hbs' : b.stacks = Function.update a.stacks 36
      (ProgramEncoding.encodeRecords (framedCandidates 2 r)) := by
    simpa [graphCharactersPorts,ha.dimension] using hbs
  have hbframe (j : Fin 44) (hj : j ≠ 36) : b.stacks j = a.stacks j := by
    rw [hbs',Function.update_of_ne hj]
  have hgt : GenerateReady (projectState graphGenerateRegisters graphTuplesPorts b) := by
    refine ⟨?_,?_,?_⟩
    · intro i; fin_cases i <;> apply Eq.trans (hbframe _ (by decide)) <;> apply graphEmpty ha <;> decide
    · exact (hbframe 38 (by decide)).trans (graphEmpty ha 38 (by decide) (by decide) (by decide) (by decide))
    · exact (hbframe 37 (by decide)).trans (graphEmpty ha 37 (by decide) (by decide) (by decide) (by decide))
  obtain ⟨nt,c,hnt,het,hcs,_⟩ := generate_lifted_update 2 graphGenerateRegisters graphTuplesPorts
    (Fin.castAdd_injective _ _) (by decide) b hgt
  have hb41 : b.stacks 41 = List.replicate (D * r) true := by rw [hbframe 41 (by decide)]; exact ha.entries
  have hcs' : c.stacks = Function.update b.stacks 38
      (ProgramEncoding.encodeRecords (framedCandidates 2 (D * r))) := by
    simpa [graphTuplesPorts,hb41] using hcs
  let flagged := (Atom.set 19 false).eval c
  let base := projectState id graphSearchStacks flagged
  have hwork (i : Fin 40) (h30 : i ≠ 30) (h31 : i ≠ 31) (h32 : i ≠ 32)
      (h36 : i ≠ 36) (h38 : i ≠ 38) : base.stacks i = [] := by
    change c.stacks (graphSearchStacks i) = []
    rw [hcs',hbs']
    have h36' : graphSearchStacks i ≠ 36 := by
      intro h; apply h36; exact Fin.ext (by simpa [graphSearchStacks] using congrArg Fin.val h)
    have h38' : graphSearchStacks i ≠ 38 := by
      intro h; apply h38; exact Fin.ext (by simpa [graphSearchStacks] using congrArg Fin.val h)
    simp only [Function.update_of_ne h36',Function.update_of_ne h38']
    exact ha.work i h30 h31 h32
  have hready : GraphOuterReady D r q qbits Dbits base := by
    constructor
    · intro i
      apply hwork <;> intro h <;> have hv := congrArg Fin.val h <;> simp only at hv <;> omega
    · change c.stacks 30 = _; rw [hcs',hbs']; exact ha.rows
    · change c.stacks 31 = _; rw [hcs',hbs']; exact ha.qword
    · change c.stacks 32 = _; rw [hcs',hbs']; exact ha.Dword
    · exact hwork 33 (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hwork 34 (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hwork 35 (by decide) (by decide) (by decide) (by decide) (by decide)
    · change c.stacks 36 = _; rw [hcs',hbs']; rfl
    · exact hwork 37 (by decide) (by decide) (by decide) (by decide) (by decide)
    · have h := hwork 29 (by decide) (by decide) (by decide) (by decide) (by decide)
      change (base.stacks 29).length ≤ _
      rw [h]; exact Nat.zero_le _
    · exact ha.qvalue
    · exact ha.Dvalue
  have hinv : GraphInvariant D r q qbits Dbits base := by
    refine ⟨hready,?_⟩
    simp [base,flagged,projectState,Atom.eval,Atom.instr,execInstr,
      StructuredProgram.State.ofCfg]
  obtain ⟨out,tail,s,hgood,hout,ns,hns,hs⟩ := graph_search_exists hq hsize base hinv
    (base.regs 17) (base.regs 18) (base.regs 19)
  have hsource : base.stacks 38 = ProgramEncoding.encodeRecords (framedCandidates 2 (D * r)) := by
    change c.stacks 38 = _; rw [hcs']; rfl
  have hentry : RecordPrograms.state graphOuterPorts base (base.regs 17) (base.regs 18)
      (base.regs 19) (ProgramEncoding.encodeRecords (framedCandidates 2 (D * r))) [] = base :=
    RecordPrograms.state_eq_self _ _ _ _ _ _ _ rfl rfl rfl hsource
      (hwork 39 (by decide) (by decide) (by decide) (by decide) (by decide))
  rw [hentry] at hs
  let small := RecordPrograms.state graphOuterPorts out false true true tail []
  let final := embedState id graphSearchStacks flagged small
  have hcall := eval_call_from_state graphSearchProgram id graphSearchStacks flagged
    Function.injective_id (Fin.castAdd_injective _ _) hs
  have hfinal : final.stacks 29 = matrixFrames s := by
    have h := embedState_stack id graphSearchStacks flagged small (Fin.castAdd_injective _ _) 29
    exact h.trans (by simpa [small,RecordPrograms.state,graphOuterPorts] using hout)
  refine ⟨final,s,hgood,hfinal,nc+(nt+(1+ns))+1,?_,?_⟩
  · have hlenc : (a.stacks (graphCharactersPorts 9)).length = r := by simp [graphCharactersPorts,ha.dimension]
    have hlent : (b.stacks (graphTuplesPorts 9)).length = D * r := by simp [graphTuplesPorts,hb41]
    rw [hlenc] at hnc
    rw [hlent] at hnt
    unfold graphProgramBudget
    omega
  · exact compiled_halt_trace (hec.seq (het.seq ((Eval.base (.atom _ c)).seq hcall))) 40 29

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
