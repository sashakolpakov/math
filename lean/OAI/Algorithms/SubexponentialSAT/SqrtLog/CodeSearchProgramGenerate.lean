import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramDepth
import OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionSupport
import OAI.Algorithms.SubexponentialSAT.SubexpSetupFrames
import OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! A closed storage wrapper for tuple generation. Only p is fixed in the
instruction table (we use p=2 and p=3); the tuple depth is read at runtime.
The literal alphabet, preserved depth copy, output copy, and scratch cleanup
are all paid bit operations. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open SubexponentialSAT.Subexp.TupleProgram SubexponentialSAT.SubexpEnumerationPayload

abbrev GenerateState := State 16 12

def generateRegisters : Fin 10 → Fin 16 := Fin.castAdd 6
def generateStacks : Fin 9 → Fin 12 := Fin.castAdd 3
def seedRegisters : Fin 8 → Fin 16 := Fin.castAdd 8
def generateWork : List (Fin 12) := List.ofFn generateStacks

def alphabetBits (p : ℕ) [Fact p.Prime] := ProgramEncoding.encodeRecords (framedAlphabet p)

abbrev generateCommand (p : ℕ) [Fact p.Prime] : Cmd 16 12 :=
  .seq (liftCommand (ArithmeticExpressionSupport.pushWord 1 (alphabetBits p))
    0 1 seedRegisters id) <|
  .seq (copyCmd 9 8 11) <|
  .seq (.call (ProgramLinking.liftProgram enumerationProgram generateRegisters generateStacks)) <|
  .seq (copyCmd 0 10 11) (clearMany generateWork)

def generateProgram (p : ℕ) [Fact p.Prime] := compiled (generateCommand p) 9 10

def generateBudget (p d : ℕ) [Fact p.Prime] :=
  100 * ((alphabetBits p).length + d + framedEnumerationCost p d + 1)

def GenerateReady (a : GenerateState) : Prop :=
  (∀ i : Fin 9, a.stacks (generateStacks i) = []) ∧ a.stacks 10 = [] ∧ a.stacks 11 = []

private theorem arbitrary_generator {p : ℕ} [Fact p.Prime] (a : State 10 9)
    (ha : a.stacks 1 = alphabetBits p)
    (he : ∀ i : Fin 9, i ≠ 1 → i ≠ 8 → a.stacks i = []) :
    ∃ b : State 10 9, b.stacks 0 = ProgramEncoding.encodeRecords
      (framedCandidates p (a.stacks 8).length) ∧
      RunsIn enumerationProgram (framedEnumerationCost p (a.stacks 8).length)
        (a.withPC (some enumerationProgram.entry)) (b.withPC none) := by
  have hi : outerInvariant (framedAlphabet p) (a.stacks 8) (a.regs 9) a := by
    exact ⟨ha,he 3 (by decide) (by decide),he 4 (by decide) (by decide),
      he 6 (by decide) (by decide),he 7 (by decide) (by decide),rfl,rfl⟩
  obtain ⟨b,hb,n,hn,ht⟩ := generateProgram_runsIn (framedAlphabet p) (a.stacks 8)
    (a.regs 9) a hi (he 0 (by decide) (by decide))
      (he 2 (by decide) (by decide)) (he 5 (by decide) (by decide))
  have hw : ∀ word ∈ framedAlphabet p, word.length ≤ 2 * scalarWidth p + 1 := by
    intro word hword
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hword
    exact ((framedScalarCode p).length_block x).le
  have hc := SubexponentialSAT.Subexp.PackingTupleBounds.generated_powerCost_le
    (framedAlphabet p) (a.stacks 8).length (2 * scalarWidth p + 1) hw
  refine ⟨b,hb.2.1,n,?_,ht⟩
  exact hn.trans (by simpa [framedEnumerationCost] using Nat.add_le_add_right hc 9)

private theorem workCost (ps : List (Fin 12)) (a : GenerateState) (B : ℕ)
    (ha : ∀ i ∈ ps, (a.stacks i).length ≤ B) :
    clearManyCost ps a ≤ ps.length * (2 * B + 3) := by
  induction ps generalizing a with
  | nil => simp [clearManyCost]
  | cons p ps ih =>
      have hc := ih (clearState p a) (by
        intro i hi
        by_cases hip : i = p
        · simp [clearState,hip]
        · simpa [clearState,hip] using ha i (by simp [hi]))
      have hp := ha p (by simp)
      simp only [clearManyCost,List.length_cons]
      nlinarith

theorem generate_eval (p : ℕ) [Fact p.Prime] (a : GenerateState) (ha : GenerateReady a) :
    ∃ (n : ℕ) (out : GenerateState), n + 1 ≤ generateBudget p (a.stacks 9).length ∧
      Eval (generateCommand p) n a out ∧
      out.stacks 10 = ProgramEncoding.encodeRecords (framedCandidates p (a.stacks 9).length) ∧
      out.stacks 9 = a.stacks 9 ∧ out.stacks 11 = [] ∧
      (∀ i : Fin 9, out.stacks (generateStacks i) = []) := by
  obtain ⟨rf,hseed⟩ := ArithmeticExpressionSupport.pushWord_eval (1 : Fin 12)
    (alphabetBits p) (projectState seedRegisters id a)
  let seed : State 8 12 := ⟨rf,Function.update a.stacks 1 (alphabetBits p ++ a.stacks 1)⟩
  let b := embedState seedRegisters id a seed
  have hb := eval_liftCommand_from_state (ArithmeticExpressionSupport.pushWord 1 (alphabetBits p))
    0 1 seedRegisters id a (Fin.castAdd_injective _ _) Function.injective_id hseed
  have hbs (i : Fin 12) : b.stacks i = Function.update a.stacks 1 (alphabetBits p) i := by
    rw [show b.stacks i = seed.stacks i from
      embedState_stack seedRegisters id a seed Function.injective_id i]
    have h1 := ha.1 1
    change a.stacks 1 = [] at h1
    simp [seed,h1]
  have hb11 : b.stacks 11 = [] := by rw [hbs]; exact ha.2.2
  let c := copyState 9 8 b
  have hc := copy_eval 9 8 11 b (by decide) (by decide) (by decide) hb11
  have hcs (i : Fin 12) : c.stacks i =
      if i = 8 then a.stacks 9 else if i = 1 then alphabetBits p else a.stacks i := by
    have h8 := ha.1 8
    change a.stacks 8 = [] at h8
    by_cases hi8 : i = 8 <;> by_cases hi1 : i = 1 <;>
      simp [c,copyState,StackRoutines.copyStacks,hbs,h8,hi8,hi1]
  let small := projectState generateRegisters generateStacks c
  have hs1 : small.stacks 1 = alphabetBits p := by simp [small,projectState,generateStacks,hcs]
  have hs8 : small.stacks 8 = a.stacks 9 := by simp [small,projectState,generateStacks,hcs]
  have hse (i : Fin 9) (hi1 : i ≠ 1) (hi8 : i ≠ 8) : small.stacks i = [] := by
    have h1 : generateStacks i ≠ 1 := by
      intro h; apply hi1; apply Fin.ext; simpa [generateStacks] using congrArg Fin.val h
    have h8 : generateStacks i ≠ 8 := by
      intro h; apply hi8; apply Fin.ext; simpa [generateStacks] using congrArg Fin.val h
    change c.stacks (generateStacks i) = []
    rw [hcs,ite_eq_right h8,ite_eq_right h1]
    exact ha.1 i
  obtain ⟨result,hr0,ng,hng,hg⟩ := arbitrary_generator small hs1 hse
  rw [hs8] at hr0 hng
  let d := embedState generateRegisters generateStacks c result
  have hstart : embedState generateRegisters generateStacks c small = c :=
    embedState_project generateRegisters generateStacks c (Fin.castAdd_injective _ _)
      (Fin.castAdd_injective _ _)
  have hd := eval_call_lifted enumerationProgram generateRegisters generateStacks c
    (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _) hg
  rw [hstart] at hd
  have hds (i : Fin 9) : d.stacks (generateStacks i) = result.stacks i :=
    embedState_stack generateRegisters generateStacks c result (Fin.castAdd_injective _ _) i
  have hdf (i : Fin 12) (hi : 9 ≤ i.val) : d.stacks i = a.stacks i := by
    rw [show d.stacks i = c.stacks i from embedState_stack_frame _ _ _ _ i (by
      rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      simp [generateStacks] at hv
      omega)]
    rw [hcs,ite_eq_right (by intro h; subst i; omega),ite_eq_right (by intro h; subst i; omega)]
  let B := (alphabetBits p).length + (a.stacks 9).length + framedEnumerationCost p (a.stacks 9).length
  have hsmall (i : Fin 9) : (result.stacks i).length ≤ B := by
    have h := SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le hg i
    have hinput : (small.stacks i).length ≤ (alphabetBits p).length + (a.stacks 9).length := by
      by_cases hi1 : i = 1
      · subst i; rw [hs1]; omega
      by_cases hi8 : i = 8
      · subst i; rw [hs8]; omega
      rw [hse i hi1 hi8]; simp
    change (result.stacks i).length ≤ (small.stacks i).length + ng at h
    dsimp [B]
    omega
  have hd11 : d.stacks 11 = [] := (hdf 11 (by decide)).trans ha.2.2
  let e := copyState 0 10 d
  have he := copy_eval 0 10 11 d (by decide) (by decide) (by decide) hd11
  have hework (i : Fin 9) : e.stacks (generateStacks i) = result.stacks i := by
    rw [copyState_frame 0 10 _ _ (by
      intro h; have hv := congrArg Fin.val h; simp [generateStacks] at hv; omega)]
    exact hds i
  have hclean := clearMany_eval generateWork e
  have hcleancost := workCost generateWork e B (by
    intro i hi
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
    rw [hework]
    exact hsmall j)
  have hwlen : generateWork.length = 9 := by simp [generateWork]
  rw [hwlen] at hcleancost
  have hd0 : d.stacks 0 = result.stacks 0 := hds 0
  have hdcost : (d.stacks 0).length ≤ B := by rw [hd0]; exact hsmall 0
  have hb9 : b.stacks 9 = a.stacks 9 := by rw [hbs]; rfl
  let out := clearManyState generateWork e
  refine ⟨(2 * (alphabetBits p).length + 1) +
    ((7 * (b.stacks 9).length + 5) + (ng +
      ((7 * (d.stacks 0).length + 5) + clearManyCost generateWork e))),out,?_,
    hb.seq (hc.seq (hd.seq (he.seq hclean))),?_,?_,?_,?_⟩
  · rw [hb9]
    unfold generateBudget
    dsimp [B] at *
    omega
  · rw [show out.stacks 10 = e.stacks 10 from by
      rw [clearMany_stacks,ite_eq_right]
      simp [generateWork,generateStacks]]
    change d.stacks 0 ++ d.stacks 10 = _
    rw [hd0,hr0,hdf 10 (by decide),ha.2.1,List.append_nil]
  · rw [show out.stacks 9 = e.stacks 9 from by
      rw [clearMany_stacks,ite_eq_right]
      simp [generateWork,generateStacks]]
    rw [copyState_frame 0 10 9 d (by decide)]
    exact hdf 9 (by decide)
  · rw [show out.stacks 11 = e.stacks 11 from by
      rw [clearMany_stacks,ite_eq_right]
      simp [generateWork,generateStacks]]
    exact (copyState_frame 0 10 11 d (by decide)).trans hd11
  · intro i
    have hm : generateStacks i ∈ generateWork := List.mem_ofFn.mpr ⟨i,rfl⟩
    rw [clearMany_stacks,ite_eq_left hm]

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
