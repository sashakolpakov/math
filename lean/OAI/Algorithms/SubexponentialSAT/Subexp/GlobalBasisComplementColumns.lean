import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisColumns
import OAI.Algorithms.SubexponentialSAT.SubexpLocalBatchParse
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-!
# Complement descriptors from actual local-search records

The input is a reverse-order list of local-search payloads.  Each iteration
decodes the stored dimensions, computes their difference using the parser's
actual unary-pop loop, and emits exactly the corresponding complement
columns.  Countdown color indices and prepending restore ascending order.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisComplementColumns

open BitProgram StructuredCalls
open GlobalBasisColumns (unary Descriptor record segmentPrefix segmentCost)

abbrev Data := State 8 22
abbrev Code := Cmd 8 22

structure LocalData where
  N : ℕ
  rank : ℕ
  table : List Bool

def LocalData.payload (q : LocalData) := SubexpLocalBatchParse.payload q.N q.rank q.table

def cleanPorts : List (Fin 22) := [2, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]
def Ready (d : Data) : Prop := ∀ i ∈ cleanPorts, d.stacks i = []

def popTag : Code := .base (.atom (.pop 10 0 1))
def popped (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 (d.stacks 10).head?, Function.update d.stacks 10 (d.stacks 10).tail⟩
def readNext : Code := .seq popTag (MatrixProgramSupport.readWord 10 12 11 (by decide))

theorem readNext_eval (bits tail : List Bool) (d : Data)
    (hs : d.stacks 10 = record bits ++ tail) (h11 : d.stacks 11 = [])
    (h12 : d.stacks 12 = []) :
    ∃ e, Eval readNext (9 * bits.length + 8) d e ∧
      e.stacks = Function.update (Function.update d.stacks 10 tail) 12 bits := by
  have hp : Eval popTag 1 d (popped d) := .base (.atom _ _)
  obtain ⟨e, he, hse⟩ := MatrixProgramSupport.readWord_eval 10 12 11
    (by decide) (by decide) (by decide) (popped d) bits tail
    (by simp [popped, hs, record]) (by simp [popped, h12]) (by simp [popped, h11])
  refine ⟨e, ?_, ?_⟩
  · have h := hp.seq he
    convert h using 1
    all_goals first | rfl | omega
  · rw [hse]
    funext i
    fin_cases i <;> simp [popped]

def parsePorts : Fin 12 → Fin 22 := ![12, 13, 4, 14, 5, 15, 16, 17, 18, 19, 20, 21]
theorem parsePorts_injective : Function.Injective parsePorts := by decide
def parse : Code := liftCommand SubexpLocalBatchParse.command 0 3 id parsePorts

def parsedStacks (d : Data) (q : LocalData) :=
  Function.update (Function.update (Function.update (Function.update d.stacks
    13 (unary q.N)) 4 (unary q.rank)) 14 q.table) 5 (unary (q.N - q.rank))

theorem parse_eval (q : LocalData) (d : Data)
    (hs : d.stacks 12 = q.payload)
    (hc : ∀ i : Fin 12, i ≠ 0 → d.stacks (parsePorts i) = []) :
    ∃ e, Eval parse (SubexpLocalBatchParse.cost q.N q.rank q.table + 1) d e ∧
      e.stacks = parsedStacks d q := by
  obtain ⟨b, hb, hbs⟩ := SubexpLocalBatchParse.command_eval q.N q.rank q.table
    (projectState id parsePorts d) hs hc
  refine ⟨embedState id parsePorts d b,
    eval_liftCommand_from_state _ 0 3 id parsePorts d Function.injective_id parsePorts_injective hb, ?_⟩
  change Function.extend parsePorts b.stacks d.stacks = _
  rw [hbs]
  simp only [SubexpLocalBatchParse.resultStacks,
    ProgramLinking.extend_update parsePorts_injective]
  have hp := congrArg StructuredProgram.State.stacks
    (embedState_project id parsePorts d Function.injective_id parsePorts_injective)
  change Function.extend parsePorts (projectState id parsePorts d).stacks d.stacks = d.stacks at hp
  rw [hp]
  rfl

def segmentPorts (i : Fin 10) : Fin 22 := Fin.castAdd 12 i
theorem segmentPorts_injective : Function.Injective segmentPorts := Fin.castAdd_injective 10 12
def segment : Code := liftCommand GlobalBasisColumns.segment 5 3 id segmentPorts

theorem segment_eval (block color offset count : ℕ) (d : Data)
    (h0 : d.stacks 0 = unary block) (h1 : d.stacks 1 = unary color)
    (h2 : d.stacks 2 = []) (h4 : d.stacks 4 = unary offset)
    (h5 : d.stacks 5 = unary count) (h6 : d.stacks 6 = [])
    (h7 : d.stacks 7 = []) (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = []) :
    ∃ e, Eval segment (segmentCost block color offset count + 1) d e ∧
      e.stacks = Function.update (Function.update d.stacks 5 []) 3
        (segmentPrefix block color offset count ++ d.stacks 3) := by
  obtain ⟨b, hb, hbs⟩ := GlobalBasisColumns.segment_eval block color offset count
    (projectState id segmentPorts d) h0 h1 h2 h4 h5 h6 h7 h8 h9
  refine ⟨embedState id segmentPorts d b,
    eval_liftCommand_from_state _ 5 3 id segmentPorts d Function.injective_id segmentPorts_injective hb, ?_⟩
  change Function.extend segmentPorts b.stacks d.stacks = _
  rw [hbs, ProgramLinking.extend_update segmentPorts_injective,
    ProgramLinking.extend_update segmentPorts_injective]
  have hp := congrArg StructuredProgram.State.stacks
    (embedState_project id segmentPorts d Function.injective_id segmentPorts_injective)
  change Function.extend segmentPorts (projectState id segmentPorts d).stacks d.stacks = d.stacks at hp
  rw [hp]
  rfl

def clear (src : Fin 22) : Code := .call (StackRoutines.clearProgram src 0 1)
def cleared (src : Fin 22) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩

theorem clear_eval (src : Fin 22) (d : Data) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared src d) :=
  .call _ (ListRegisterProgram.clear_run src (0 : Fin 8) 1 d.regs d.stacks)

def cleanup : Code := .seq (clear 4) (.seq (clear 12) (.seq (clear 13) (clear 14)))
def cleaned (d : Data) := cleared 14 (cleared 13 (cleared 12 (cleared 4 d)))

theorem cleanup_eval (d : Data) :
    Eval cleanup (2 * ((d.stacks 4).length + (d.stacks 12).length +
      (d.stacks 13).length + (d.stacks 14).length) + 12) d (cleaned d) := by
  have h := (clear_eval 4 d).seq ((clear_eval 12 (cleared 4 d)).seq
    ((clear_eval 13 (cleared 12 (cleared 4 d))).seq
      (clear_eval 14 (cleared 13 (cleared 12 (cleared 4 d))))))
  convert h using 1
  all_goals first | rfl | (simp [cleared]; omega)

def step : Code := .seq readNext (.seq parse (.seq segment cleanup))
def stepCost (block color : ℕ) (q : LocalData) : ℕ :=
  (9 * q.payload.length + 8) + (SubexpLocalBatchParse.cost q.N q.rank q.table + 1) +
    (segmentCost block color q.rank (q.N - q.rank) + 1) +
      (2 * (q.rank + q.payload.length + q.N + q.table.length) + 12)

theorem step_eval (block color : ℕ) (q : LocalData) (tail : List Bool) (d : Data)
    (h0 : d.stacks 0 = unary block) (h1 : d.stacks 1 = unary color)
    (hs : d.stacks 10 = record q.payload ++ tail) (hr : Ready d) :
    ∃ e, Eval step (stepCost block color q) d e ∧
      e.stacks = Function.update (Function.update d.stacks 10 tail) 3
        (segmentPrefix block color q.rank (q.N - q.rank) ++ d.stacks 3) := by
  obtain ⟨a, ha, hsa⟩ := readNext_eval q.payload tail d hs
    (hr 11 (by simp [cleanPorts])) (hr 12 (by simp [cleanPorts]))
  have hclean : ∀ i : Fin 12, i ≠ 0 → a.stacks (parsePorts i) = [] := by
    intro i hi
    fin_cases i <;> simp_all [ parsePorts, Ready, cleanPorts]
  obtain ⟨b, hb, hsb⟩ := parse_eval q a (by simp [hsa]) hclean
  obtain ⟨c, hc, hsc⟩ := segment_eval block color q.rank (q.N - q.rank) b
    (by simp [hsb, parsedStacks, hsa, h0])
    (by simp [hsb, parsedStacks, hsa, h1])
    (by simpa [hsb, parsedStacks, hsa] using hr 2 (by simp [cleanPorts]))
    (by simp [hsb, parsedStacks]) (by simp [hsb, parsedStacks])
    (by simpa [hsb, parsedStacks, hsa] using hr 6 (by simp [cleanPorts]))
    (by simpa [hsb, parsedStacks, hsa] using hr 7 (by simp [cleanPorts]))
    (by simpa [hsb, parsedStacks, hsa] using hr 8 (by simp [cleanPorts]))
    (by simpa [hsb, parsedStacks, hsa] using hr 9 (by simp [cleanPorts]))
  refine ⟨cleaned c, ?_, ?_⟩
  · have h := ha.seq (hb.seq (hc.seq (cleanup_eval c)))
    convert h using 1
    all_goals first
      | rfl
      | (simp [stepCost, hsc, hsb, parsedStacks, hsa, unary]; omega)
  · funext i
    have h4 := hr 4 (by simp [cleanPorts])
    have h5 := hr 5 (by simp [cleanPorts])
    have h12 := hr 12 (by simp [cleanPorts])
    have h13 := hr 13 (by simp [cleanPorts])
    have h14 := hr 14 (by simp [cleanPorts])
    fin_cases i <;> simp [cleaned, cleared, hsc, hsb, parsedStacks, hsa,
      h4, h5, h12, h13, h14]

def loopPorts : UnaryForPrograms.Ports 8 22 := ⟨1, 0, 1⟩
def colors : Code := UnaryForPrograms.forCmd loopPorts step
def encoded (qs : List LocalData) := Encoding.encodeList LocalData.payload qs

def colorPrefix (block : ℕ) : List LocalData → List Bool
  | [] => []
  | q :: qs => colorPrefix block qs ++ segmentPrefix block qs.length q.rank (q.N - q.rank)

def colorCost (block : ℕ) : List LocalData → ℕ
  | [] => 2
  | q :: qs => stepCost block qs.length q + colorCost block qs + 2

theorem colors_visits (block : ℕ) (qs : List LocalData) (suffix : List Bool) :
    ∀ d : Data, d.stacks 0 = unary block → d.stacks 1 = unary qs.length →
      d.stacks 10 = encoded qs ++ suffix → Ready d →
      ∃ costs e, UnaryForPrograms.Visits loopPorts step costs (colorCost block qs) d e ∧
        e.stacks = Function.update (Function.update (Function.update d.stacks 1 [])
          10 (false :: suffix)) 3 (colorPrefix block qs ++ d.stacks 3) := by
  induction qs with
  | nil =>
    intro d h0 h1 hs hr
    refine ⟨[], UnaryForPrograms.popped loopPorts d, .done d h1, ?_⟩
    funext i
    fin_cases i <;> simp_all [UnaryForPrograms.popped, loopPorts, colorPrefix, encoded,
      Encoding.encodeList, unary]
  | cons q qs ih =>
    intro d h0 h1 hs hr
    let p := UnaryForPrograms.popped loopPorts d
    have hp0 : p.stacks 0 = unary block := by simp [p, UnaryForPrograms.popped, loopPorts, h0]
    have hp1 : p.stacks 1 = unary qs.length := by
      simp [p, UnaryForPrograms.popped, loopPorts, h1, unary, List.replicate_succ]
    have hpr : Ready p := by
      intro i hi
      have hi1 : i ≠ 1 := by intro he; subst i; simp [cleanPorts] at hi
      simpa [p, UnaryForPrograms.popped, loopPorts, hi1] using hr i hi
    obtain ⟨e, he, hse⟩ := step_eval block qs.length q (encoded qs ++ suffix) p hp0 hp1
      (by simp [p, UnaryForPrograms.popped, loopPorts, hs, encoded,
        Encoding.encodeList, record, List.append_assoc]) hpr
    have her : Ready e := by
      intro i hi
      have hi3 : i ≠ 3 := by intro he; subst i; simp [cleanPorts] at hi
      have hi10 : i ≠ 10 := by intro he; subst i; simp [cleanPorts] at hi
      simpa [hse, hi3, hi10] using hpr i hi
    obtain ⟨costs, f, hf, hsf⟩ := ih e
      (by simp [hse, hp0]) (by simp [hse, hp1]) (by simp [hse]) her
    refine ⟨stepCost block qs.length q :: costs, f,
      .step (by simp [loopPorts, h1, unary]) he (by simp [hse, loopPorts, p]) hf, ?_⟩
    funext i
    fin_cases i <;> simp [hsf, hse, p, UnaryForPrograms.popped, loopPorts,
      colorPrefix, List.append_assoc]

theorem colors_eval (block : ℕ) (qs : List LocalData) (suffix : List Bool) (d : Data)
    (h0 : d.stacks 0 = unary block) (h1 : d.stacks 1 = unary qs.length)
    (hs : d.stacks 10 = encoded qs ++ suffix) (hr : Ready d) :
    ∃ e, Eval colors (colorCost block qs) d e ∧
      e.stacks = Function.update (Function.update (Function.update d.stacks 1 [])
        10 (false :: suffix)) 3 (colorPrefix block qs ++ d.stacks 3) := by
  obtain ⟨costs, e, he, hse⟩ := colors_visits block qs suffix d h0 h1 hs hr
  exact ⟨e, he.eval, hse⟩

end SubexponentialSAT.Subexp.GlobalBasisComplementColumns

end OAI.Algorithms
