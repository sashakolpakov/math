import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ParserProgram
import OAI.Algorithms.SubexponentialSAT.CounterPrograms
import OAI.Algorithms.SubexponentialSAT.ProgramLinking
import OAI.Algorithms.SubexponentialSAT.BitProgramCompile

namespace OAI.Algorithms

/-!
# Actual initialization of the canonical SAT input

The nineteen-label program splits the variable-count header and counts its
unary marks into a binary stack word. The untouched encoded CNF body remains
on stack 0. All growing values live on Boolean stacks, not in finite control.
-/

namespace SubexponentialSAT.FrontendProgram

open SubexponentialSAT.BitProgram

/-- Body, unary work, binary variable count, and counter scratch. -/
def storage (body unary binary scratch : List Bool) : Fin 4 → List Bool :=
  fun i => if i = 0 then body else if i = 1 then unary else if i = 2 then binary else scratch

@[simp] theorem storage_zero (a b c d : List Bool) : storage a b c d 0 = a := rfl
@[simp] theorem storage_one (a b c d : List Bool) : storage a b c d 1 = b := rfl
@[simp] theorem storage_two (a b c d : List Bool) : storage a b c d 2 = c := rfl
@[simp] theorem storage_three (a b c d : List Bool) : storage a b c d 3 = d := rfl

def cfg (pc : Option (Fin 19)) (b p : Bool) (body unary binary scratch : List Bool) :
    Cfg 3 4 19 := ⟨pc, CounterPrograms.counterRegs b p false, storage body unary binary scratch⟩

/-- The port maps are fixed once. Counter input/output/scratch are stacks 1/2/3. -/
abbrev initializeProgram : Program 3 4 19 :=
  ProgramLinking.linkInto ParserProgram.natProgram CounterPrograms.lengthProgram
    Fin.castSucc (Fin.castAdd 2) id Fin.succ

def emptyFrame : Cfg 3 4 19 := cfg none false false [] [] [] []
def bodyFrame (body : List Bool) : Cfg 3 4 19 := cfg none false false body [] [] []

theorem extend_parser_regs (b p : Bool) :
    Function.extend (Fin.castSucc : Fin 2 → Fin 3) (ParserProgram.pair b p)
      (CounterPrograms.counterRegs false false false) = CounterPrograms.counterRegs b p false := by
  funext i
  fin_cases i
  · exact (Fin.castSucc_injective 2).extend_apply _ _ 0
  · exact (Fin.castSucc_injective 2).extend_apply _ _ 1
  · have hn : ¬ ∃ j : Fin 2, j.castSucc = (2 : Fin 3) := by
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      have hl := j.isLt
      change j.val = 2 at hv
      omega
    exact Function.extend_apply' _ _ _ hn

theorem extend_parser_stacks (body unary : List Bool) :
    Function.extend (Fin.castAdd 2 : Fin 2 → Fin 4) (ParserProgram.pair body unary)
      (storage [] [] [] []) = storage body unary [] [] := by
  funext i
  fin_cases i
  · exact (Fin.castAdd_injective 2 2).extend_apply _ _ 0
  · exact (Fin.castAdd_injective 2 2).extend_apply _ _ 1
  · have hn : ¬ ∃ j : Fin 2, j.castAdd 2 = (2 : Fin 4) := by
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      have hl := j.isLt
      change j.val = 2 at hv
      omega
    exact Function.extend_apply' _ _ _ hn
  · have hn : ¬ ∃ j : Fin 2, j.castAdd 2 = (3 : Fin 4) := by
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      have hl := j.isLt
      change j.val = 3 at hv
      omega
    exact Function.extend_apply' _ _ _ hn

theorem extend_counter_stacks (body unary binary scratch : List Bool) :
    Function.extend (Fin.succ : Fin 3 → Fin 4)
      (CounterPrograms.lengthStacks unary binary scratch) (storage body [] [] []) =
      storage body unary binary scratch := by
  funext i
  fin_cases i
  · have hn : ¬ ∃ j : Fin 3, j.succ = (0 : Fin 4) := by simp
    exact Function.extend_apply' _ _ _ hn
  · exact (Fin.succ_injective 3).extend_apply _ _ 0
  · exact (Fin.succ_injective 3).extend_apply _ _ 1
  · exact (Fin.succ_injective 3).extend_apply _ _ 2

@[simp] theorem embed_parser (pc : Option (Fin 5)) (b p : Bool) (body unary : List Bool) :
    ProgramLinking.embedCfg Fin.castSucc (Fin.castAdd 2) (Fin.castAdd 14) (some 5)
      emptyFrame (ParserProgram.cfg pc b p body unary) =
      cfg (ProgramLinking.relocatePc (Fin.castAdd 14) (some 5) pc) b p body unary [] [] := by
  simp [ProgramLinking.embedCfg, emptyFrame, cfg, ParserProgram.cfg,
    extend_parser_regs, extend_parser_stacks]

@[simp] theorem embed_counter (pc : Option (Fin 14)) (b p : Bool)
    (body unary binary scratch : List Bool) :
    ProgramLinking.embedCfg id Fin.succ (Fin.natAdd 5) none (bodyFrame body)
      (⟨pc, CounterPrograms.counterRegs b p false,
        CounterPrograms.lengthStacks unary binary scratch⟩ : Cfg 3 3 14) =
      cfg (ProgramLinking.relocatePc (Fin.natAdd 5) none pc) b p body unary binary scratch := by
  simp [ProgramLinking.embedCfg, bodyFrame, cfg, extend_counter_stacks]

theorem counter_terminal_eq (output : List Bool) :
    terminal CounterPrograms.lengthProgram output =
      (⟨none, CounterPrograms.counterRegs false false false,
        CounterPrograms.lengthStacks [] output []⟩ : Cfg 3 3 14) := by
  simp [terminal ]
  constructor
  · funext i
    simp [CounterPrograms.counterRegs]
  · funext i
    fin_cases i <;> simp [CounterPrograms.lengthStacks]

theorem initialize_initial (input : List Bool) :
    initial initializeProgram input = cfg (some 0) false false input [] [] [] := by
  simp [initial, cfg]
  constructor
  · funext i
    simp [CounterPrograms.counterRegs]
  · funext i
    fin_cases i <;> simp [storage]

theorem header_trace (n : ℕ) (body : List Bool) :
    Trace initializeProgram (4 * n + 4)
      (initial initializeProgram (Encoding.encodeNat n ++ body))
      (cfg (some 5) false true body (List.replicate n true) [] []) := by
  have h := ProgramLinking.relocate_trace ParserProgram.natProgram initializeProgram
    Fin.castSucc (Fin.castAdd 2) (Fin.castAdd 14) (some 5) emptyFrame
    (Fin.castSucc_injective 2) (Fin.castAdd_injective 2 2)
    (ProgramLinking.linkInto_leftCode ParserProgram.natProgram CounterPrograms.lengthProgram
      Fin.castSucc (Fin.castAdd 2) id Fin.succ)
    (ParserProgram.nat_trace n body [] false false)
  simpa [embed_parser, ProgramLinking.relocatePc, initialize_initial] using h

/-- The direct sum of the two checked instruction bounds. -/
def initializeBound (n : ℕ) : ℕ := (4 * n + 4) + (n * (8 * n + 10) + 3)

theorem initializeBound_eq (n : ℕ) : initializeBound n = 8 * n ^ 2 + 14 * n + 7 := by
  unfold initializeBound
  ring

theorem initializeBound_mono {n m : ℕ} (h : n ≤ m) : initializeBound n ≤ initializeBound m := by
  have hm : n * (8 * n + 10) ≤ m * (8 * m + 10) :=
    Nat.mul_le_mul h (by omega)
  unfold initializeBound
  omega

/-- Actual raw-input initialization. The formula body is preserved on stack 0,
the binary count is on stack 2, and both work stacks are empty. -/
theorem initialize_raw (n : ℕ) (body : List Bool) :
    ∃ binary : List Bool, CounterPrograms.value binary = n ∧ binary.length ≤ n ∧
      RunsIn initializeProgram (initializeBound n)
        (initial initializeProgram (Encoding.encodeNat n ++ body))
        (cfg none false false body [] binary []) := by
  obtain ⟨binary, hv, hlen, hc⟩ :=
    CounterPrograms.length_correct_from false true (List.replicate n true)
  simp only [List.length_replicate] at hv hlen hc
  have hrel := ProgramLinking.relocate_runsIn CounterPrograms.lengthProgram initializeProgram
    id Fin.succ (Fin.natAdd 5) none (bodyFrame body)
    Function.injective_id (Fin.succ_injective 3)
    (ProgramLinking.linkInto_rightCode ParserProgram.natProgram CounterPrograms.lengthProgram
      Fin.castSucc (Fin.castAdd 2) id Fin.succ) hc
  have hcounter : RunsIn initializeProgram (n * (8 * n + 10) + 3)
      (cfg (some 5) false true body (List.replicate n true) [] [])
      (cfg none false false body [] binary []) := by
    simpa [CounterPrograms.lengthCfg, counter_terminal_eq, embed_counter,
      ProgramLinking.relocatePc] using hrel
  have hheader : RunsIn initializeProgram (4 * n + 4)
      (initial initializeProgram (Encoding.encodeNat n ++ body))
      (cfg (some 5) false true body (List.replicate n true) [] []) :=
    ⟨_, le_rfl, header_trace n body⟩
  exact ⟨binary, hv, hlen, hheader.trans hcounter⟩

theorem initialize_formula {n : ℕ} (F : SAT.CNF (Fin n)) :
    ∃ binary : List Bool, CounterPrograms.value binary = n ∧ binary.length ≤ n ∧
      RunsIn initializeProgram (initializeBound (Encoding.formulaBitLength F))
        (initial initializeProgram (Encoding.encodeCNF F))
        (cfg none false false (Encoding.encodeCNFBody F) [] binary []) := by
  obtain ⟨binary, hv, hlen, hr⟩ := initialize_raw n (Encoding.encodeCNFBody F)
  refine ⟨binary, hv, hlen, ?_⟩
  exact hr.mono (initializeBound_mono (Encoding.numVariables_le_formulaBitLength F))

/-- The same fixed program applies uniformly across the dependent input type. -/
theorem initialize_sigma (F : (n : ℕ) × SAT.CNF (Fin n)) :
    ∃ binary : List Bool, CounterPrograms.value binary = F.1 ∧ binary.length ≤ F.1 ∧
      RunsIn initializeProgram (initializeBound (Encoding.encodeFormula F).length)
        (initial initializeProgram (Encoding.encodeFormula F))
        (cfg none false false (Encoding.encodeCNFBody F.2) [] binary []) := by
  rcases F with ⟨n, F⟩
  exact initialize_formula F

/-- The checked compiler gives a primitive-tape execution from the actual raw input. -/
theorem initialize_formula_primitive {n : ℕ} (F : SAT.CNF (Fin n)) :
    ∃ binary : List Bool, CounterPrograms.value binary = n ∧ binary.length ≤ n ∧
      Computation.RunsIn (primitive initializeProgram).step
        (primitiveOverhead initializeProgram * initializeBound (Encoding.formulaBitLength F))
        ((primitive initializeProgram).init (Encoding.encodeCNF F))
        (primitiveCfg initializeProgram
          (cfg none false false (Encoding.encodeCNFBody F) [] binary [])) := by
  obtain ⟨binary, hv, hlen, hr⟩ := initialize_formula F
  refine ⟨binary, hv, hlen, ?_⟩
  simpa only [primitive_initial] using primitive_execution initializeProgram hr

end SubexponentialSAT.FrontendProgram

end OAI.Algorithms
