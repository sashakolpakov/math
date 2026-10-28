import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPostfixInterpreter

namespace OAI.Algorithms

/-!
# A finite postfix interpreter with a real literal-projection call

The literal bytes are parsed and pushed by the concrete loader, then passed to
an actual finite projection service before dispatch resumes. Arithmetic and
projection contracts refer to traces of supplied Boolean instruction tables.
-/

namespace SubexponentialSAT.SubexpProjectedInterpreter

open BitProgram
open SubexpPostfixControl (triple cfg4 controlLabel literalLabel pushLoopProgram
  literalService serializeCode serializeInstr operandDepth)
open SubexpPostfixInterpreter (register stack cfg castAdd_injective embed_cfg4
  embed_control_cfg bootProgram bootProgram_trace Implements)

variable {r s a b c : ℕ}

def baseLabel : Fin 37 → Fin (37 + (2 + (a + (b + c)))) := Fin.castAdd _
def bootLabel (i : Fin 2) : Fin (37 + (2 + (a + (b + c)))) :=
  Fin.natAdd 37 (Fin.castAdd (a + (b + c)) i)
def addLabel (i : Fin a) : Fin (37 + (2 + (a + (b + c)))) :=
  Fin.natAdd 37 (Fin.natAdd 2 (Fin.castAdd (b + c) i))
def mulLabel (i : Fin b) : Fin (37 + (2 + (a + (b + c)))) :=
  Fin.natAdd 37 (Fin.natAdd 2 (Fin.natAdd a (Fin.castAdd c i)))
def loadLabel (i : Fin c) : Fin (37 + (2 + (a + (b + c)))) :=
  Fin.natAdd 37 (Fin.natAdd 2 (Fin.natAdd a (Fin.natAdd b i)))

/-- All three services are installed as finite instruction-table regions. -/
def program (add : Program (3 + r) (4 + s) a) (mul : Program (3 + r) (4 + s) b)
    (loader : Program (3 + r) (4 + s) c) :
    Program (3 + r) (4 + s) (37 + (2 + (a + (b + c)))) where
  inputStack := stack 0
  outputStack := stack 2
  entry := bootLabel 0
  code := Fin.addCases
    (fun pc : Fin 37 =>
      if pc = 16 then .goto (addLabel add.entry)
      else if pc = 17 then .goto (mulLabel mul.entry)
      else if pc = 36 then .goto (loadLabel loader.entry)
      else ProgramLinking.relocateInstr register stack baseLabel none (pushLoopProgram.code pc))
    (Fin.addCases
      (fun pc : Fin 2 => if pc = 0 then .set (register 0) false (bootLabel 1)
        else .push (stack 2) (register 0) (baseLabel 0))
      (Fin.addCases
        (fun pc : Fin a => ProgramLinking.relocateInstr id id addLabel (some (baseLabel 0)) (add.code pc))
        (Fin.addCases
          (fun pc : Fin b => ProgramLinking.relocateInstr id id mulLabel (some (baseLabel 0)) (mul.code pc))
          (fun pc : Fin c => ProgramLinking.relocateInstr id id loadLabel (some (baseLabel 0))
            (loader.code pc)))))

variable (add : Program (3 + r) (4 + s) a) (mul : Program (3 + r) (4 + s) b)
  (loader : Program (3 + r) (4 + s) c)

theorem program_base_code (pc : Fin 37) (h16 : pc ≠ 16) (h17 : pc ≠ 17) (h36 : pc ≠ 36) :
    (program add mul loader).code (baseLabel pc) =
      ProgramLinking.relocateInstr register stack baseLabel none (pushLoopProgram.code pc) := by
  simp [program, baseLabel, h16, h17, h36]

theorem program_add_code : ProgramLinking.CodeEmbedding add (program add mul loader)
    id id addLabel (some (baseLabel 0)) := by
  intro pc
  simp [program, addLabel]

theorem program_mul_code : ProgramLinking.CodeEmbedding mul (program add mul loader)
    id id mulLabel (some (baseLabel 0)) := by
  intro pc
  simp [program, mulLabel]

theorem program_load_code : ProgramLinking.CodeEmbedding loader (program add mul loader)
    id id loadLabel (some (baseLabel 0)) := by
  intro pc
  simp [program, loadLabel]

theorem program_control_nonhalt (pc : Fin 20)
    (hp : SubexpPostfixControl.program.code pc ≠ .halt) :
    (program add mul loader).code (baseLabel (controlLabel pc)) =
      ProgramLinking.relocateInstr register (fun i => stack (Fin.castAdd 1 i))
        (fun i => baseLabel (controlLabel i)) none (SubexpPostfixControl.program.code pc) := by
  fin_cases pc <;> first | rfl | simp [] at hp

/-- The loader's final halt now jumps into the supplied projection table. -/
theorem program_literal_code : ProgramLinking.CodeEmbedding literalService (program add mul loader)
    register stack (fun i => baseLabel (literalLabel i)) (some (loadLabel loader.entry)) := by
  intro pc
  fin_cases pc <;> rfl

theorem prepare_literal_trace (context : Fin s → List Bool)
    (code depth operands : List Bool) (v p op : Bool) :
    Trace (program add mul loader) 6
      (cfg (some (baseLabel 0)) v p op (false :: code) depth operands context)
      (cfg (some (baseLabel 20)) true true op code (true :: depth) operands context) := by
  have h := ProgramLinking.relocate_trace_before_halt SubexpPostfixControl.program
    (program add mul loader) register (fun i => stack (Fin.castAdd 1 i))
    (fun i => baseLabel (controlLabel i)) none
    (cfg none false false false [] [] [] context)
    (castAdd_injective 3 r) ((castAdd_injective 4 s).comp (castAdd_injective 3 1))
    (program_control_nonhalt add mul loader)
    (SubexpPostfixControl.prepare_push_trace v p op code depth operands)
    (by simp [SubexpPostfixControl.cfg])
  rw [embed_control_cfg, embed_control_cfg] at h
  have hc : Trace (program add mul loader) 1
      (cfg (some (baseLabel 15)) true true op code (true :: depth) operands context)
      (cfg (some (baseLabel 20)) true true op code (true :: depth) operands context) := by
    refine .cons ?_ (.refl _)
    change some (execInstr ((program add mul loader).code (baseLabel 15)) _) = _
    rfl
  exact h.trans hc

/-- Parse all literal bytes and enter projection with its raw payload on top. -/
theorem raw_push_trace (context : Fin s → List Bool)
    (bits rest depth operands : List Bool) (v p op : Bool) :
    Trace (program add mul loader) (11 * bits.length + 17)
      (cfg (some (baseLabel 0)) v p op (false :: (Encoding.frame bits ++ rest)) depth operands context)
      (cfg (some (loadLabel loader.entry)) true false op rest (true :: depth)
        (true :: (Encoding.frame bits ++ operands)) context) := by
  have hl := ProgramLinking.relocate_trace literalService (program add mul loader)
    register stack (fun i => baseLabel (literalLabel i)) (some (loadLabel loader.entry))
    (cfg none false false false [] [] [] context)
    (castAdd_injective 3 r) (castAdd_injective 4 s) (program_literal_code add mul loader)
    (SubexpPostfixControl.literalService_trace bits rest (true :: depth) operands true true op)
  rw [embed_cfg4, embed_cfg4] at hl
  have h := (prepare_literal_trace add mul loader context (Encoding.frame bits ++ rest)
    depth operands v p op).trans hl
  convert h using 1
  · omega
  · simp [ProgramLinking.relocatePc]

theorem binary_prepare_trace (context : Fin s → List Bool)
    (isMul : Bool) (code operands : List Bool)
    (depth : List Bool) (v p op : Bool) :
    Trace (program add mul loader) 13
      (cfg (some (baseLabel 0)) v p op (true :: isMul :: code)
        (true :: true :: depth) operands context)
      (cfg (some (baseLabel (if isMul then 17 else 16))) true true isMul
        code (true :: depth) operands context) := by
  have h := ProgramLinking.relocate_trace_before_halt SubexpPostfixControl.program (program add mul loader)
    register (fun i => stack (Fin.castAdd 1 i)) (fun i => baseLabel (controlLabel i)) none
    (cfg none false false false [] [] [] context)
    (castAdd_injective 3 r) ((castAdd_injective 4 s).comp (castAdd_injective 3 1))
    (program_control_nonhalt add mul loader)
    (SubexpPostfixControl.prepare_binary_trace isMul true true v p op code depth operands) (by simp [SubexpPostfixControl.cfg])
  rw [embed_control_cfg, embed_control_cfg] at h
  cases isMul <;> exact h

theorem add_call_step (context : Fin s → List Bool) (code depth operands : List Bool) :
    step (program add mul loader) (cfg (some (baseLabel 16)) true true false code depth operands context) =
      some (cfg (some (addLabel add.entry)) true true false code depth operands context) := by
  simp [step, cfg, program, baseLabel, execInstr]

theorem mul_call_step (context : Fin s → List Bool) (code depth operands : List Bool) :
    step (program add mul loader) (cfg (some (baseLabel 17)) true true true code depth operands context) =
      some (cfg (some (mulLabel mul.entry)) true true true code depth operands context) := by
  simp [step, cfg, program, baseLabel, execInstr]

def bootMap : Fin 3 → Fin (37 + (2 + (a + (b + c)))) :=
  triple (bootLabel 0) (bootLabel 1) (baseLabel 0)

theorem boot_nonhalt (pc : Fin 3) (hp : bootProgram.code pc ≠ .halt) :
    (program add mul loader).code (bootMap pc) =
      ProgramLinking.relocateInstr register stack bootMap none (bootProgram.code pc) := by
  fin_cases pc <;> first | rfl | simp [] at hp

theorem boot_trace (context : Fin s → List Bool) (code : List Bool) :
    Trace (program add mul loader) 2
      (cfg (some (program add mul loader).entry) false false false code [] [] context)
      (cfg (some (baseLabel 0)) false false false code [] [false] context) := by
  have h := ProgramLinking.relocate_trace_before_halt bootProgram (program add mul loader)
    register stack bootMap none (cfg none false false false [] [] [] context)
    (castAdd_injective 3 r) (castAdd_injective 4 s)
    (boot_nonhalt add mul loader) (bootProgram_trace code) (by simp [])
  rw [embed_cfg4, embed_cfg4] at h
  exact h

theorem finish_trace (context : Fin s → List Bool) (depth operands : List Bool) (v p op : Bool) :
    Trace (program add mul loader) 3
      (cfg (some (baseLabel 0)) v p op [] depth operands context)
      (cfg none false false op [] depth operands context) := by
  have h := ProgramLinking.relocate_trace_before_halt SubexpPostfixControl.program (program add mul loader)
    register (fun i => stack (Fin.castAdd 1 i)) (fun i => baseLabel (controlLabel i)) none
    (cfg none false false false [] [] [] context)
    (castAdd_injective 3 r) ((castAdd_injective 4 s).comp (castAdd_injective 3 1))
    (program_control_nonhalt add mul loader) (SubexpPostfixControl.eof_trace v p op depth operands)
    (by simp [SubexpPostfixControl.cfg])
  rw [embed_control_cfg, embed_control_cfg] at h
  have hc : (program add mul loader).code (baseLabel 18) = .halt := by
    rw [program_base_code add mul loader 18 (by decide) (by decide) (by decide)]
    rfl
  have hs : Trace (program add mul loader) 1
      (cfg (some (baseLabel 18)) false false op [] depth operands context)
      (cfg none false false op [] depth operands context) := by
    refine .cons ?_ (.refl _)
    change some (execInstr ((program add mul loader).code (baseLabel 18)) _) = _
    rw [hc]
    rfl
  exact h.trans hs


end SubexponentialSAT.SubexpProjectedInterpreter

end OAI.Algorithms
