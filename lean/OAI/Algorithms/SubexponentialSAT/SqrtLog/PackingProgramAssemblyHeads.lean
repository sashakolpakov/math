import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramAssemblyHeadSetup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidatesLift

namespace OAI.Algorithms

/-! Actual head-score production from the controller table and alphabet. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

def headRegisters (i : Fin 8) : Fin 16 := i.castAdd 8
theorem headRegisters_injective : Function.Injective headRegisters := Fin.castAdd_injective _ _

def headPorts : Fin 12 → Fin 48 := ![3,1,4,5,6,2,7,13,14,12,15,16]
theorem headPorts_injective : Function.Injective headPorts := by decide

abbrev copyAlphabet : Cmd 16 48 := .call (SubexponentialSAT.StackRoutines.copyProgram 30 14 17 0 1)
abbrev resetHead : Cmd 16 48 := SequentialProgram.resetList (List.finRange 16)
abbrev headCandidates : Cmd 16 48 := PackingHeadProgramCandidates.lifted headRegisters headPorts
abbrev headCleanup : Cmd 16 48 := SequentialProgram.clearList [1,2,18]
abbrev heads : Cmd 16 48 := .seq headSetup (.seq copyAlphabet
  (.seq resetHead (.seq headCandidates headCleanup)))

def HeadReady (d : Data) : Prop := ∀ j : Fin 48,
  j ∈ ({1,2,3,4,5,6,7,12,13,14,15,16,17,18} : Finset (Fin 48)) → d.stacks j=[]

theorem headRows_flatten_length {r Q : ℕ} (heads : ℕ) (fixed : List (Word r Q)) :
    (headRows heads fixed).flatten.length=headCount heads fixed*ReadPlan.wordWidth r Q := by
  unfold headRows headCount
  split
  · simpa using encodedWords_length fixed.reverse
  · simp

theorem headScoreRecords_eq {r Q : ℕ} (heads : ℕ) (fixed alphabet : List (Word r Q)) :
    PackingHeadProgramCandidates.scoreRecords (headRows heads fixed) (alphabet.map ReadPlan.encodeWord) =
      alphabet.map (fun candidate => UnaryCompare.encode (overlap heads fixed candidate)) := by
  simp [PackingHeadProgramCandidates.scoreRecords,PackingHeadProgramCandidates.scoreBits,
    overlap,UnaryCompare.encode,List.map_map,Function.comp_def]

def headsBudget {r Q : ℕ} (d : Data) (headCount : ℕ) (fixed alphabet : List (Word r Q)) : ℕ :=
  PackingWeightProgram.Gate.budget (projectState gateRegisters gatePorts d)+1+
  PackingPrefixProgram.budget (Assembly.headCount headCount fixed) (ReadPlan.wordWidth r Q)+1+
  (7*(d.stacks 30).length+5)+16+
  PackingHeadProgramCandidates.budget (headRows headCount fixed) (alphabet.map ReadPlan.encodeWord)+
  3*(2*(Assembly.headCount headCount fixed*ReadPlan.wordWidth r Q+Assembly.headCount headCount fixed)+3)

theorem heads_eval {r Q : ℕ} (d : Data) (headCount : ℕ) (fixed alphabet : List (Word r Q))
    (padding : List Bool) (hr : HeadReady d)
    (hhead : SubexponentialSAT.CounterPrograms.value (d.stacks 20)=headCount)
    (hp : (d.stacks 19).length=fixed.length)
    (hw : (d.stacks 10).length=ReadPlan.wordWidth r Q)
    (ha : d.stacks 8=(fixed.reverse.map ReadPlan.encodeWord).flatten++padding)
    (halphabet : d.stacks 30=ProgramEncoding.encodeRecords (alphabet.map ReadPlan.encodeWord)) :
    ∃ t ≤ headsBudget d headCount fixed alphabet, ∃ e : Data,
      Eval heads t d e ∧
      e.stacks 12=ProgramEncoding.encodeRecords
        (alphabet.map (fun candidate => UnaryCompare.encode (overlap headCount fixed candidate))) ∧
      (∀ j,j≠12→e.stacks j=d.stacks j) := by
  have hready : SetupReady d := by
    intro j hj
    exact hr j ((show ({1,2,3,4,5,6,7,13,18} : Finset (Fin 48)) ⊆
      {1,2,3,4,5,6,7,12,13,14,15,16,17,18} by decide) hj)
  obtain ⟨ts,hts,b,hs,hb1,hb2,hb18,hbf⟩ := headSetup_eval d headCount fixed padding hready hhead hp hw ha
  have hb14 : b.stacks 14=[] := (hbf _ (by decide) (by decide) (by decide)).trans (hr _ (by simp))
  have hb17 : b.stacks 17=[] := (hbf _ (by decide) (by decide) (by decide)).trans (hr _ (by simp))
  have hb30 : b.stacks 30=d.stacks 30 := hbf _ (by decide) (by decide) (by decide)
  let a := SubexponentialSAT.SubexpScanPrimitives.afterCopy b 30 14 0 1
  have hcopy : Eval copyAlphabet (7*(b.stacks 30).length+5) b a :=
    SubexponentialSAT.SubexpScanPrimitives.copy_eval b 30 14 17 0 1 (by decide) (by decide) (by decide) (by decide) hb17
  have hstack : a.stacks=Function.update b.stacks 14 (b.stacks 30) := by
    funext j
    simp [a,SubexponentialSAT.SubexpScanPrimitives.afterCopy,SubexponentialSAT.StackRoutines.copyStacks,hb14]
  let z := SequentialProgram.resetState (List.finRange 16) a
  have hreset : Eval resetHead 16 a z := SequentialProgram.resetList_eval _ _
  have hzstack : z.stacks=Function.update b.stacks 14 (b.stacks 30) := hstack
  have hzregs : ∀ i,z.regs (headRegisters i)=false := by
    intro i
    simp [z]
  have hz1 : z.stacks (headPorts 1)=(headRows headCount fixed).flatten := by
    simpa [hzstack,headPorts] using hb1
  have hz5 : z.stacks (headPorts 5)=List.replicate (headRows headCount fixed).length true := by
    simpa [hzstack,headPorts,headRows_length] using hb2
  have hz8 : z.stacks (headPorts 8)=ProgramEncoding.encodeRecords (alphabet.map ReadPlan.encodeWord) := by
    simp [hzstack,headPorts,hb30,halphabet]
  have hzero : ∀ i : Fin 12,i≠1→i≠5→i≠8→z.stacks (headPorts i)=[] := by
    intro i hi1 hi5 hi8
    fin_cases i <;> first
      | exact False.elim (hi1 rfl)
      | exact False.elim (hi5 rfl)
      | exact False.elim (hi8 rfl)
      | simpa [hzstack,headPorts,hbf] using hr _ (by simp)
  have hvalid : ∀ candidate ∈ alphabet.map ReadPlan.encodeWord,
      PackingHeadProgramCandidates.validPayload (headRows headCount fixed) candidate := by
    intro candidate hc row hrow
    obtain ⟨word,_,rfl⟩ := List.mem_map.mp hc
    simpa using headRows_width headCount fixed row hrow
  obtain ⟨tc,htc,c,hc,hcs,_,_⟩ := PackingHeadProgramCandidates.command_lifted
    headRegisters headPorts headRegisters_injective headPorts_injective z
    (headRows headCount fixed) (alphabet.map ReadPlan.encodeWord)
    hzregs hz1 hz5 hz8 hzero hvalid
  have hc1 : c.stacks 1=(headRows headCount fixed).flatten := by simpa [hcs,headPorts,hzstack] using hb1
  have hc2 : c.stacks 2=List.replicate (Assembly.headCount headCount fixed) true := by
    simpa [hcs,headPorts,hzstack] using hb2
  have hc18 : (c.stacks 18).length=Assembly.headCount headCount fixed := by
    simpa [hcs,headPorts,hzstack] using hb18
  have hlength : ∀ j ∈ ([1,2,18] : List (Fin 48)),
      (c.stacks j).length ≤ Assembly.headCount headCount fixed*ReadPlan.wordWidth r Q+Assembly.headCount headCount fixed := by
    intro j hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl
    · rw [hc1,headRows_flatten_length]; omega
    · rw [hc2,List.length_replicate]; omega
    · rw [hc18]; omega
  obtain ⟨tl,htl,e,hl,hes⟩ := SequentialProgram.clearList_eval [1,2,18] c _ hlength
  refine ⟨ts+((7*(b.stacks 30).length+5)+(16+(tc+tl))),?_,e,
    hs.seq (hcopy.seq (hreset.seq (hc.seq hl))),?_,?_⟩
  · simp only [List.length_cons,List.length_nil] at htl
    rw [hb30]
    unfold headsBudget
    omega
  · rw [hes]
    simp [hcs,headPorts,headScoreRecords_eq]
  · intro j hj12
    rw [hes]
    by_cases hj1 : j=1
    · subst j; simp [hr 1 (by simp)]
    by_cases hj2 : j=2
    · subst j; simp [hr 2 (by simp)]
    by_cases hj18 : j=18
    · subst j; simp [hr 18 (by simp)]
    by_cases hj14 : j=14
    · subst j; simp [hcs,headPorts,hr 14 (by simp)]
    · simp only [List.mem_cons,List.not_mem_nil,hj1,hj2,hj18,or_self,ite_false]
      simpa [hcs,headPorts,hzstack,hj12,hj14] using hbf j hj1 hj2 hj18

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
