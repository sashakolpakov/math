import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ScalarAlphabetFrames
import OAI.Algorithms.SubexponentialSAT.Subexp.ScalarOneProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchPreparation
import OAI.Algorithms.SubexponentialSAT.SubexpAlphabetProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-!
# Actual scalar-alphabet and constant preparation

The input is one canonical binary prime word. A fixed countdown emits all
field words, a fixed record map frames each scalar token, and copy/pop/push
instructions produce the constants needed by the two finite searches.
-/

namespace SubexponentialSAT.Subexp.ScalarSetupProgram

open BitProgram StructuredCalls TupleProgram MatrixWordEncoding
open BlockSearchPreparation (restrictState lifted_call)

def rawAlphabet (p : ℕ) [Fact p.Prime] : Records :=
  (QuarticSearch.elements p).map (word p)

def tokenAlphabet (p : ℕ) [Fact p.Prime] : Records :=
  ((rawAlphabet p).map Encoding.frame).reverse

@[simp] theorem rawAlphabet_length (p : ℕ) [Fact p.Prime] :
    (rawAlphabet p).length = p := by simp [rawAlphabet]

@[simp] theorem tokenAlphabet_length (p : ℕ) [Fact p.Prime] :
    (tokenAlphabet p).length = p := by simp [tokenAlphabet]

theorem tokenAlphabet_eq (p : ℕ) [Fact p.Prime] :
    tokenAlphabet p = (QuarticSearch.elements p).reverse.map (fun x => Encoding.frame (word p x)) := by
  simp [tokenAlphabet,rawAlphabet,List.map_reverse,List.map_map,Function.comp_def]

theorem rawAlphabet_mem (p : ℕ) [Fact p.Prime] (x : ZMod p) :
    word p x ∈ rawAlphabet p :=
  List.mem_map.mpr ⟨x,QuarticSearch.mem_elements p x,rfl⟩

theorem width_eq (p : ℕ) : width p = SubexpEnumerationPayload.scalarWidth p := by
  simp [width,SubexpLiftRing.baseWidth,SubexpEnumerationPayload.scalarWidth]

theorem rawAlphabet_eq (p : ℕ) [Fact p.Prime] :
    SubexpAlphabetProgram.alphabetWords (SubexpAlphabetProgram.primeWord p) =
      rawAlphabet p := by
  rw [SubexpAlphabetProgram.alphabetWords_primeWord]
  simp [rawAlphabet,SubexpEnumerationPayload.scalarCode,
    SubexpEnumerationPayload.scalarBits,word,width_eq]

theorem append_false_value (bits : List Bool) :
    BinaryArithmetic.toNat (bits ++ [false]) = BinaryArithmetic.toNat bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [BinaryArithmetic.toNat,ih]

theorem prime_append_false (p : ℕ) :
    SubexpAlphabetProgram.primeWord p ++ [false] = modulus p := by
  apply SubexpModulusConstruction.bits_eq_of_length_of_value
  · simp [width_eq]
  · rw [append_false_value,modulus_value]
    simpa only [CounterPrograms.value_eq_toNat] using
      SubexpAlphabetProgram.primeWord_value p

def state (regs : Fin 6 → Bool) (zero raw tokens one mod : List Bool) : State 6 9 :=
  ⟨regs,fun i => if i = 0 then zero else if i = 5 then raw else if i = 6 then tokens
    else if i = 7 then one else if i = 8 then mod else []⟩

def alphabetStacks (i : Fin 6) : Fin 9 := Fin.castAdd 3 i
def frameStacks : Fin 7 → Fin 9 := ![5,1,2,3,4,6,7]

theorem alphabetStacks_injective : Function.Injective alphabetStacks :=
  Fin.castAdd_injective _ _
theorem frameStacks_injective : Function.Injective frameStacks := by decide

abbrev makeModulus : Cmd 6 9 :=
  .seq (pushConst 8 3 false) (.call (StackRoutines.copyProgram 0 8 7 3 4))

abbrev alphabet : Cmd 6 9 :=
  .call (ProgramLinking.liftProgram SubexpAlphabetProgram.program id alphabetStacks)

abbrev reframe : Cmd 6 9 :=
  .call (ProgramLinking.liftProgram ScalarAlphabetFrames.program id frameStacks)

abbrev command : Cmd 6 9 :=
  .seq makeModulus (.seq alphabet (.seq reframe (ScalarOneProgram.command 0 7 1 3 4)))

def program := compiled command 0 6

def inputState (p : ℕ) (regs : Fin 6 → Bool) : State 6 9 :=
  state regs (SubexpAlphabetProgram.primeWord p) [] [] [] []

def outputState (p : ℕ) [Fact p.Prime] (regs : Fin 6 → Bool) : State 6 9 :=
  state regs (word p 0) (ProgramEncoding.encodeRecords (rawAlphabet p))
    (ProgramEncoding.encodeRecords (tokenAlphabet p)) (word p 1) (modulus p)

def budget (p : ℕ) [Fact p.Prime] : ℕ :=
  (p + 1) * (60 * width p + 60) + ScalarAlphabetFrames.budget (rawAlphabet p) +
    14 * width p + 16

theorem frames_budget_eq (records : Records) :
    ScalarAlphabetFrames.budget records =
      41 * (records.map List.length).sum + 44 * records.length + 18 := by
  have hb : RecordPrograms.budget (fun bits => 21 * bits.length + 23) records =
      27 * (records.map List.length).sum + 30 * records.length := by
    induction records with
    | nil => simp [RecordPrograms.budget]
    | cons x xs ih =>
        simp only [RecordPrograms.budget,List.map_cons,List.sum_cons,List.length_cons,ih]
        ring
  rw [ScalarAlphabetFrames.budget,ProgramEncoding.encodeRecords_length,hb]
  ring

theorem budget_eq (p : ℕ) [Fact p.Prime] :
    budget p = 101 * p * width p + 104 * p + 74 * width p + 94 := by
  rw [budget,frames_budget_eq]
  simp only [rawAlphabet, List.map_map]
  simp only [Function.comp_def,word_length,List.map_const',QuarticSearch.length_elements,
    List.sum_replicate_nat,List.length_map]
  ring

theorem budget_le (p : ℕ) [Fact p.Prime] :
    budget p ≤ 200 * (p + 1) * (width p + 1) := by
  rw [budget_eq]
  nlinarith

theorem makeModulus_eval (p : ℕ) (regs : Fin 6 → Bool) :
    ∃ regs', Eval makeModulus (7 * width p + 7) (inputState p regs)
      (state regs' (SubexpAlphabetProgram.primeWord p) [] [] [] (modulus p)) := by
  let a := inputState p regs
  let b := pushedState 8 3 false a
  let c : State 6 9 := ⟨readRegs b.regs 3 4 none,StackRoutines.copyStacks 0 8 b.stacks⟩
  have h1 := pushConst_eval 8 3 false a
  have h2 := copy_eval 0 8 7 3 4 (by decide) (by decide) (by decide) (by decide) b
    (by simp [b, a, inputState, state])
  have hc : c = state c.regs (SubexpAlphabetProgram.primeWord p) [] [] [] (modulus p) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;>
      simp [b, a, inputState, state, StackRoutines.copyStacks, prime_append_false]
  have he := h1.seq h2
  change Eval _ _ a c at he
  rw [hc] at he
  refine ⟨c.regs,?_⟩
  convert he using 1
  all_goals
    simp [b, a, inputState, state, width_eq]
    omega

theorem alphabet_eval (p : ℕ) [Fact p.Prime] (regs : Fin 6 → Bool) (mod : List Bool) :
    ∃ n ≤ (p + 1) * (60 * width p + 60), ∃ regs', Eval alphabet n
      (state regs (SubexpAlphabetProgram.primeWord p) [] [] [] mod)
      (state regs' (word p 0) (ProgramEncoding.encodeRecords (rawAlphabet p)) [] [] mod) := by
  let a := state regs (SubexpAlphabetProgram.primeWord p) [] [] [] mod
  obtain ⟨next,hout,⟨h2,h3,h4⟩,h1,hv,hl,hr⟩ :=
    SubexpAlphabetProgram.program_runsIn_clean (SubexpAlphabetProgram.primeWord p) regs
  have hz : next.stacks 0 = word p 0 := by
    have he := SubexpAlphabetProgram.canonical_of_width_value (next.stacks 0) (width p) 0
      (by simpa only [SubexpAlphabetProgram.primeWord_length,← width_eq p] using hl) hv
    simpa [word] using he
  rw [rawAlphabet_eq] at hout
  have ha : restrictState id alphabetStacks a =
      SubexpAlphabetProgram.inputState (SubexpAlphabetProgram.primeWord p) regs := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [alphabetStacks, a, state]
  obtain ⟨n,hn,he⟩ := lifted_call SubexpAlphabetProgram.program id alphabetStacks
    Function.injective_id alphabetStacks_injective a next
    ((p + 1) * (60 * width p + 60))
    (by simpa only [ha,SubexpAlphabetProgram.primeWord_value,
      SubexpAlphabetProgram.primeWord_length,← width_eq p] using hr)
  have hnext : embedState id alphabetStacks a next =
      state next.regs (word p 0) (ProgramEncoding.encodeRecords (rawAlphabet p)) [] [] mod := by
    apply embedState_eq_of_ports id alphabetStacks a _ next
      Function.injective_id alphabetStacks_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intro i
      fin_cases i <;> simp [state,alphabetStacks,hz,h1,h2,h3,h4,hout]
    · intro i hi
      fin_cases i
      · exact False.elim (hi ⟨0,rfl⟩)
      · exact False.elim (hi ⟨1,rfl⟩)
      · exact False.elim (hi ⟨2,rfl⟩)
      · exact False.elim (hi ⟨3,rfl⟩)
      · exact False.elim (hi ⟨4,rfl⟩)
      · exact False.elim (hi ⟨5,rfl⟩)
      · rfl
      · rfl
      · rfl
  exact ⟨n,hn,next.regs,by simpa only [hnext] using he⟩

theorem restrict_reframe (records : Records) (regs : Fin 6 → Bool) (zero mod : List Bool) :
    restrictState id frameStacks
      (state regs zero (ProgramEncoding.encodeRecords records) [] [] mod) =
        ScalarAlphabetFrames.inputState records regs := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;> simp [frameStacks, state]

def frameResult (regs : Fin 6 → Bool) (raw out : List Bool) : State 6 7 :=
  ⟨regs,fun i => if i = 0 then raw else if i = 5 then out else []⟩

theorem frame_output_eq (records : Records) (regs : Fin 6 → Bool) :
    ScalarAlphabetFrames.outputState records regs = frameResult regs
      (ProgramEncoding.encodeRecords records)
      (ProgramEncoding.encodeRecords ((records.map Encoding.frame).reverse)) := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp

theorem embed_frameResult (regs nextRegs : Fin 6 → Bool) (zero raw out mod : List Bool) :
    embedState id frameStacks
      (state regs zero raw [] [] mod) (frameResult nextRegs raw out) =
        state nextRegs zero raw out [] mod := by
  apply SubexpScanPrimitives.embedState_eq id frameStacks
    Function.injective_id frameStacks_injective (state regs zero raw [] [] mod)
    (state nextRegs zero raw out [] mod) (frameResult nextRegs raw out)
  · intro i; rfl
  · intro i
    fin_cases i <;> rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i hi
    fin_cases i
    · rfl
    · exact False.elim (hi ⟨1,rfl⟩)
    · exact False.elim (hi ⟨2,rfl⟩)
    · exact False.elim (hi ⟨3,rfl⟩)
    · exact False.elim (hi ⟨4,rfl⟩)
    · exact False.elim (hi ⟨0,rfl⟩)
    · exact False.elim (hi ⟨5,rfl⟩)
    · exact False.elim (hi ⟨6,rfl⟩)
    · rfl

theorem embed_reframe (records : Records) (regs nextRegs : Fin 6 → Bool) (zero mod : List Bool) :
    embedState id frameStacks
      (state regs zero (ProgramEncoding.encodeRecords records) [] [] mod)
      (ScalarAlphabetFrames.outputState records nextRegs) =
        state nextRegs zero (ProgramEncoding.encodeRecords records)
          (ProgramEncoding.encodeRecords ((records.map Encoding.frame).reverse)) [] mod := by
  rw [frame_output_eq]
  exact embed_frameResult regs nextRegs zero _ _ mod

theorem reframe_eval (p : ℕ) [Fact p.Prime] (regs : Fin 6 → Bool) (zero mod : List Bool) :
    ∃ n ≤ ScalarAlphabetFrames.budget (rawAlphabet p), ∃ regs', Eval reframe n
      (state regs zero (ProgramEncoding.encodeRecords (rawAlphabet p)) [] [] mod)
      (state regs' zero (ProgramEncoding.encodeRecords (rawAlphabet p))
        (ProgramEncoding.encodeRecords (tokenAlphabet p)) [] mod) := by
  obtain ⟨r,hr⟩ := ScalarAlphabetFrames.program_run (rawAlphabet p) regs
  obtain ⟨n,hn,he⟩ := lifted_call ScalarAlphabetFrames.program id frameStacks
    Function.injective_id frameStacks_injective
    (state regs zero (ProgramEncoding.encodeRecords (rawAlphabet p)) [] [] mod)
    (ScalarAlphabetFrames.outputState (rawAlphabet p) r)
    (ScalarAlphabetFrames.budget (rawAlphabet p))
    (by simpa only [restrict_reframe] using hr)
  refine ⟨n,hn,r,?_⟩
  simpa only [reframe,embed_reframe,tokenAlphabet] using he

theorem program_run (p : ℕ) [Fact p.Prime] (regs : Fin 6 → Bool) :
    ∃ regs', RunsIn program (budget p)
      ((inputState p regs).withPC (some program.entry)) ((outputState p regs').withPC none) := by
  obtain ⟨r1,h1⟩ := makeModulus_eval p regs
  obtain ⟨n2,hn2,r2,h2⟩ := alphabet_eval p r1 (modulus p)
  obtain ⟨n3,hn3,r3,h3⟩ := reframe_eval p r2 (word p 0) (modulus p)
  obtain ⟨r4,h4⟩ := ScalarOneProgram.canonical_eval p (0 : Fin 9) 7 1 (3 : Fin 6) 4
    (by decide) (by decide) (by decide) (by decide)
    (state r3 (word p 0) (ProgramEncoding.encodeRecords (rawAlphabet p))
      (ProgramEncoding.encodeRecords (tokenAlphabet p)) [] (modulus p)) rfl rfl rfl
  have hend : (⟨r4,Function.update
      (state r3 (word p 0) (ProgramEncoding.encodeRecords (rawAlphabet p))
        (ProgramEncoding.encodeRecords (tokenAlphabet p)) [] (modulus p)).stacks 7 (word p 1)⟩ :
        State 6 9) = outputState p r4 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [state]
  rw [hend] at h4
  have he := h1.seq (h2.seq (h3.seq h4))
  refine ⟨r4,_,?_,compiled_halt_trace he 0 6⟩
  dsimp [budget]
  omega

end SubexponentialSAT.Subexp.ScalarSetupProgram

end OAI.Algorithms
