import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPostfixControl

namespace OAI.Algorithms

/-!
# A finite postfix interpreter with linked arithmetic services

The interpreter contains the concrete tag dispatcher and literal loader, two
initialization instructions, and the supplied finite arithmetic instruction
tables. Arithmetic correctness is required as a local Boolean-machine trace
contract; an arithmetic operation is never added to the instruction language.
-/

namespace SubexponentialSAT.SubexpPostfixInterpreter

open BitProgram
open SubexpPostfixControl

variable {r s a b : ℕ}

def register : Fin 3 → Fin (3 + r) := Fin.castAdd r
def stack : Fin 4 → Fin (4 + s) := Fin.castAdd s

def baseLabel : Fin 37 → Fin (37 + (2 + (a + b))) := Fin.castAdd _
def bootLabel (i : Fin 2) : Fin (37 + (2 + (a + b))) :=
  Fin.natAdd 37 (Fin.castAdd (a + b) i)
def addLabel (i : Fin a) : Fin (37 + (2 + (a + b))) :=
  Fin.natAdd 37 (Fin.natAdd 2 (Fin.castAdd b i))
def mulLabel (i : Fin b) : Fin (37 + (2 + (a + b))) :=
  Fin.natAdd 37 (Fin.natAdd 2 (Fin.natAdd a i))

/-- Scratch stack 3 is empty. Additional stacks carry the fixed arithmetic
context, including empty scratch slots and persistent ring parameters. -/
def cfg {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin s → List Bool := fun _ => []) :
    Cfg (3 + r) (4 + s) l where
  pc := pc
  regs := Fin.addCases (triple v p op) (fun _ => false)
  «stacks» := Fin.addCases (quadruple code depth operands []) context

theorem castAdd_injective (m n : ℕ) : Function.Injective (@Fin.castAdd m n) := by
  intro x y h
  exact Fin.ext (congrArg (fun i : Fin (m + n) => i.val) h)

theorem extend_castAdd {m n : ℕ} {α : Type*} (f : Fin m → α) (z : α) :
    Function.extend (Fin.castAdd n) f (fun _ => z) =
      Fin.addCases f (fun _ : Fin n => z) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa using (castAdd_injective m n).extend_apply f (fun _ => z) j
  · intro j
    rw [Function.extend_apply' _ _ _ ?_]
    · simp
    · rintro ⟨k, hk⟩
      have hv := congrArg Fin.val hk
      change k.val = m + j.val at hv
      omega

theorem extend_two_castAdd {m n k : ℕ} {α : Type*} (f : Fin m → α) (z : α) :
    Function.extend (fun i => Fin.castAdd k (Fin.castAdd n i)) f (fun _ => z) =
      Fin.addCases (Fin.addCases f (fun _ : Fin n => z)) (fun _ : Fin k => z) := by
  have hi : Function.Injective (fun i => Fin.castAdd k (Fin.castAdd n i)) :=
    (castAdd_injective (m + n) k).comp (castAdd_injective m n)
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro h
      simpa only [Function.comp_apply, Fin.addCases_left] using
        hi.extend_apply f (fun _ => z) h
    · intro h
      rw [Function.extend_apply' _ _ _ ?_]
      · simp
      · rintro ⟨v, hv⟩
        have he := congrArg Fin.val hv
        change v.val = m + h.val at he
        omega
  · intro j
    rw [Function.extend_apply' _ _ _ ?_]
    · simp
    · rintro ⟨v, hv⟩
      have he := congrArg Fin.val hv
      change v.val = m + n + j.val at he
      omega

private theorem quad_three (code depth operands : List Bool) :
    quadruple code depth operands [] =
      Fin.addCases (motive := fun _ : Fin (3 + 1) => List Bool)
        (triple code depth operands) (fun _ : Fin 1 => []) := by
  funext i
  fin_cases i <;> rfl

theorem extend_castAdd_frame {m n : ℕ} {α : Type*} (f f0 : Fin m → α) (g : Fin n → α) :
    Function.extend (Fin.castAdd n) f (Fin.addCases f0 g) = Fin.addCases f g := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa using (castAdd_injective m n).extend_apply f (Fin.addCases f0 g) j
  · intro j
    rw [Function.extend_apply' _ _ _ ?_]
    · simp
    · rintro ⟨v, hv⟩
      have h := congrArg Fin.val hv
      change v.val = m + j.val at h
      omega

theorem extend_two_castAdd_frame {m n k : ℕ} {α : Type*}
    (f f0 : Fin m → α) (g : Fin n → α) (h : Fin k → α) :
    Function.extend (fun i => Fin.castAdd k (Fin.castAdd n i)) f
      (Fin.addCases (Fin.addCases f0 g) h) = Fin.addCases (Fin.addCases f g) h := by
  have hi : Function.Injective (fun i => Fin.castAdd k (Fin.castAdd n i)) :=
    (castAdd_injective (m + n) k).comp (castAdd_injective m n)
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro v
      simpa only [Function.comp_apply, Fin.addCases_left] using
        hi.extend_apply f (Fin.addCases (Fin.addCases f0 g) h) v
    · intro v
      rw [Function.extend_apply' _ _ _ ?_]
      · simp
      · rintro ⟨w, hw⟩
        have he := congrArg Fin.val hw
        change w.val = m + v.val at he
        omega
  · intro j
    rw [Function.extend_apply' _ _ _ ?_]
    · simp
    · rintro ⟨v, hv⟩
      have he := congrArg Fin.val hv
      change v.val = m + n + j.val at he
      omega

private theorem cfg_ext {R S L : ℕ} {x y : Cfg R S L}
    (hp : x.pc = y.pc) (hr : x.regs = y.regs) (hs : x.stacks = y.stacks) : x = y := by
  cases x; cases y; simp_all

theorem embed_cfg4 {l L : ℕ} (context : Fin s → List Bool)
    (label : Fin l → Fin L) (ret : Option (Fin L))
    (pc : Option (Fin l)) (v p op : Bool) (code depth operands : List Bool) :
    ProgramLinking.embedCfg (@register r) (@stack s) label ret
      (cfg (r := r) (s := s) none false false false [] [] [] context)
      (cfg4 pc v p op code depth operands []) =
    cfg (ProgramLinking.relocatePc label ret pc) v p op code depth operands context := by
  apply cfg_ext
  · rfl
  · change Function.extend (Fin.castAdd r) (triple v p op) _ = _
    have hf : (cfg (r := r) (s := s) (l := L) none false false false [] [] [] context).regs =
        fun _ => false := by
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; fin_cases j <;> rfl
      · intro j; simp [cfg]
    rw [hf]
    exact extend_castAdd _ _
  · exact extend_castAdd_frame _ _ _

theorem embed_control_cfg {L : ℕ} (context : Fin s → List Bool)
    (label : Fin 20 → Fin L) (ret : Option (Fin L))
    (pc : Option (Fin 20)) (v p op : Bool) (code depth operands : List Bool) :
    ProgramLinking.embedCfg (@register r) (fun i => stack (Fin.castAdd 1 i)) label ret
      (cfg (r := r) (s := s) none false false false [] [] [] context)
      (SubexpPostfixControl.cfg pc v p op code depth operands) =
    cfg (ProgramLinking.relocatePc label ret pc) v p op code depth operands context := by
  apply cfg_ext
  · rfl
  · change Function.extend (Fin.castAdd r) (triple v p op) _ = _
    have hf : (cfg (r := r) (s := s) (l := L) none false false false [] [] [] context).regs =
        fun _ => false := by
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; fin_cases j <;> rfl
      · intro j; simp [cfg]
    rw [hf]
    exact extend_castAdd _ _
  · change Function.extend (fun i => Fin.castAdd s (Fin.castAdd 1 i))
      (triple code depth operands) (Fin.addCases (quadruple [] [] [] []) context) = _
    simp only [cfg, quad_three]
    exact extend_two_castAdd_frame _ _ _ _

/-- A finite table, with actual jumps into and out of both arithmetic services. -/
abbrev program (add : Program (3 + r) (4 + s) a) (mul : Program (3 + r) (4 + s) b) :
    Program (3 + r) (4 + s) (37 + (2 + (a + b))) where
  inputStack := stack 0
  outputStack := stack 2
  entry := bootLabel 0
  code := Fin.addCases
    (fun pc : Fin 37 =>
      if pc = 16 then .goto (addLabel add.entry)
      else if pc = 17 then .goto (mulLabel mul.entry)
      else ProgramLinking.relocateInstr register stack baseLabel none (pushLoopProgram.code pc))
    (Fin.addCases
      (fun pc : Fin 2 => if pc = 0 then .set (register 0) false (bootLabel 1)
        else .push (stack 2) (register 0) (baseLabel 0))
      (Fin.addCases
        (fun pc : Fin a => ProgramLinking.relocateInstr id id addLabel (some (baseLabel 0)) (add.code pc))
        (fun pc : Fin b => ProgramLinking.relocateInstr id id mulLabel (some (baseLabel 0)) (mul.code pc))))

variable (add : Program (3 + r) (4 + s) a) (mul : Program (3 + r) (4 + s) b)

theorem program_base_code (pc : Fin 37) (h16 : pc ≠ 16) (h17 : pc ≠ 17) :
    (program add mul).code (baseLabel pc) =
      ProgramLinking.relocateInstr register stack baseLabel none (pushLoopProgram.code pc) := by
  simp [ baseLabel, h16, h17]

theorem program_add_code : ProgramLinking.CodeEmbedding add (program add mul)
    id id addLabel (some (baseLabel 0)) := by
  intro pc
  simp [ addLabel]

theorem program_mul_code : ProgramLinking.CodeEmbedding mul (program add mul)
    id id mulLabel (some (baseLabel 0)) := by
  intro pc
  simp [ mulLabel]

theorem program_base_nonhalt (pc : Fin 37) (hp : pushLoopProgram.code pc ≠ .halt) :
    (program add mul).code (baseLabel pc) =
      ProgramLinking.relocateInstr register stack baseLabel none (pushLoopProgram.code pc) := by
  apply program_base_code
  · intro h; subst pc; exact hp rfl
  · intro h; subst pc; exact hp rfl

theorem program_control_nonhalt (pc : Fin 20)
    (hp : SubexpPostfixControl.program.code pc ≠ .halt) :
    (program add mul).code (baseLabel (controlLabel pc)) =
      ProgramLinking.relocateInstr register (fun i => stack (Fin.castAdd 1 i))
        (fun i => baseLabel (controlLabel i)) none (SubexpPostfixControl.program.code pc) := by
  fin_cases pc <;> first | rfl | simp [] at hp

/-- The literal loader and all dispatcher transitions are the previously
checked instructions, relocated into this finite program. -/
theorem push_trace (context : Fin s → List Bool)
    (bits rest depth operands : List Bool) (v p op : Bool) :
    Trace (program add mul) (11 * bits.length + 17)
      (cfg (some (baseLabel 0)) v p op (false :: (Encoding.frame bits ++ rest)) depth operands context)
      (cfg (some (baseLabel 0)) true false op rest (true :: depth)
        (true :: (Encoding.frame bits ++ operands)) context) := by
  have h := ProgramLinking.relocate_trace_before_halt pushLoopProgram (program add mul)
    register stack baseLabel none (cfg none false false false [] [] [] context)
    (castAdd_injective 3 r) (castAdd_injective 4 s)
    (program_base_nonhalt add mul) (pushLoop_literal_trace bits rest depth operands v p op)
    (by simp [])
  rw [embed_cfg4, embed_cfg4] at h
  exact h

theorem binary_prepare_trace (context : Fin s → List Bool)
    (isMul : Bool) (code operands : List Bool)
    (depth : List Bool) (v p op : Bool) :
    Trace (program add mul) 13
      (cfg (some (baseLabel 0)) v p op (true :: isMul :: code)
        (true :: true :: depth) operands context)
      (cfg (some (baseLabel (if isMul then 17 else 16))) true true isMul
        code (true :: depth) operands context) := by
  have h := ProgramLinking.relocate_trace_before_halt SubexpPostfixControl.program (program add mul)
    register (fun i => stack (Fin.castAdd 1 i)) (fun i => baseLabel (controlLabel i)) none
    (cfg none false false false [] [] [] context)
    (castAdd_injective 3 r) ((castAdd_injective 4 s).comp (castAdd_injective 3 1))
    (program_control_nonhalt add mul)
    (prepare_binary_trace isMul true true v p op code depth operands) (by simp [SubexpPostfixControl.cfg])
  rw [embed_control_cfg, embed_control_cfg] at h
  cases isMul <;> exact h

theorem add_call_step (context : Fin s → List Bool) (code depth operands : List Bool) :
    step (program add mul) (cfg (some (baseLabel 16)) true true false code depth operands context) =
      some (cfg (some (addLabel add.entry)) true true false code depth operands context) := by
  simp [step, cfg, baseLabel, execInstr]

theorem mul_call_step (context : Fin s → List Bool) (code depth operands : List Bool) :
    step (program add mul) (cfg (some (baseLabel 17)) true true true code depth operands context) =
      some (cfg (some (mulLabel mul.entry)) true true true code depth operands context) := by
  simp [step, cfg, baseLabel, execInstr]

/-- The empty operand-list marker is written by two real instructions. -/
abbrev bootProgram : Program 3 4 3 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code := fun pc => if pc = 0 then .set 0 false 1
    else if pc = 1 then .push 2 0 2 else .halt

theorem bootProgram_trace (code : List Bool) :
    Trace bootProgram 2 (cfg4 (some 0) false false false code [] [] [])
      (cfg4 (some 2) false false false code [] [false] []) := by
  refine .cons (b := cfg4 (some 1) false false false code [] [] []) ?_ ?_
  · simp [step, execInstr, cfg4]
  · refine .cons ?_ (.refl _)
    simp [step, execInstr, cfg4]

def bootMap : Fin 3 → Fin (37 + (2 + (a + b))) :=
  triple (bootLabel 0) (bootLabel 1) (baseLabel 0)

theorem boot_nonhalt (pc : Fin 3) (hp : bootProgram.code pc ≠ .halt) :
    (program add mul).code (bootMap pc) =
      ProgramLinking.relocateInstr register stack bootMap none (bootProgram.code pc) := by
  fin_cases pc <;> first | rfl | simp [] at hp

theorem boot_trace (context : Fin s → List Bool) (code : List Bool) :
    Trace (program add mul) 2
      (cfg (some (program add mul).entry) false false false code [] [] context)
      (cfg (some (baseLabel 0)) false false false code [] [false] context) := by
  have h := ProgramLinking.relocate_trace_before_halt bootProgram (program add mul)
    register stack bootMap none (cfg none false false false [] [] [] context)
    (castAdd_injective 3 r) (castAdd_injective 4 s)
    (boot_nonhalt add mul) (bootProgram_trace code) (by simp [])
  rw [embed_cfg4, embed_cfg4] at h
  exact h

theorem finish_trace (context : Fin s → List Bool) (depth operands : List Bool) (v p op : Bool) :
    Trace (program add mul) 3
      (cfg (some (baseLabel 0)) v p op [] depth operands context)
      (cfg none false false op [] depth operands context) := by
  have h := ProgramLinking.relocate_trace_before_halt SubexpPostfixControl.program (program add mul)
    register (fun i => stack (Fin.castAdd 1 i)) (fun i => baseLabel (controlLabel i)) none
    (cfg none false false false [] [] [] context)
    (castAdd_injective 3 r) ((castAdd_injective 4 s).comp (castAdd_injective 3 1))
    (program_control_nonhalt add mul) (eof_trace v p op depth operands)
    (by simp [SubexpPostfixControl.cfg])
  rw [embed_control_cfg, embed_control_cfg] at h
  have hc : (program add mul).code (baseLabel 18) = .halt := by
    rw [program_base_code add mul 18 (by decide) (by decide)]
    rfl
  have hs : Trace (program add mul) 1
      (cfg (some (baseLabel 18)) false false op [] depth operands context)
      (cfg none false false op [] depth operands context) := by
    refine .cons ?_ (.refl _)
    change some (execInstr ((program add mul).code (baseLabel 18)) _) = _
    rw [hc]
    rfl
  exact h.trans hs

/-- The service contract is a trace of supplied finite Boolean instructions.
The fixed context is preserved, so it may contain modulus and width data. -/
abbrev Implements {R : Type*} {l : ℕ} (encode : R → List Bool)
    (operation : R → R → R) (isMul : Bool)
    (service : Program (3 + r) (4 + s) l) (bound : R → R → ℕ)
    (context : Fin s → List Bool) : Prop :=
  ∀ (x y : R) (xs : List R) (code depth : List Bool),
    RunsIn service (bound x y)
      (cfg (some service.entry) true true isMul code depth
        (Encoding.encodeList encode (y :: x :: xs)) context)
      (cfg none false false false code depth
        (Encoding.encodeList encode (operation x y :: xs)) context)

section Execution

variable {R : Type*} [Add R] [Mul R] (encode : R → List Bool)
variable (addBound mulBound : R → R → ℕ) (context : Fin s → List Bool)
variable (hadd : Implements encode (· + ·) false add addBound context)
variable (hmul : Implements encode (· * ·) true mul mulBound context)

include hadd in
omit [Mul R] in
theorem add_instruction (x y : R) (xs : List R) (code depth : List Bool) (v p op : Bool) :
    RunsIn (program add mul) (14 + addBound x y)
      (cfg (some (baseLabel 0)) v p op (true :: false :: code) (true :: true :: depth)
        (Encoding.encodeList encode (y :: x :: xs)) context)
      (cfg (some (baseLabel 0)) false false false code (true :: depth)
        (Encoding.encodeList encode ((x + y) :: xs)) context) := by
  obtain ⟨n, hn, ht⟩ := hadd x y xs code (true :: depth)
  have hs := ProgramLinking.relocate_trace add (program add mul) id id addLabel
    (some (baseLabel 0)) (cfg none false false false [] [] [] context)
    Function.injective_id Function.injective_id (program_add_code add mul) ht
  simp only [ProgramLinking.embedCfg_id, ProgramLinking.relabelCfg,
    ProgramLinking.relocatePc, cfg] at hs
  have hc : Trace (program add mul) 1
      (cfg (some (baseLabel 16)) true true false code (true :: depth)
        (Encoding.encodeList encode (y :: x :: xs)) context)
      (cfg (some (addLabel add.entry)) true true false code (true :: depth)
        (Encoding.encodeList encode (y :: x :: xs)) context) :=
    .cons (add_call_step add mul context code _ _) (.refl _)
  have hp := binary_prepare_trace add mul context false code
    (Encoding.encodeList encode (y :: x :: xs)) depth v p op
  have h := (hp.trans hc).trans hs
  refine ⟨13 + 1 + n, by omega, ?_⟩
  exact h

include hmul in
omit [Add R] in
theorem mul_instruction (x y : R) (xs : List R) (code depth : List Bool) (v p op : Bool) :
    RunsIn (program add mul) (14 + mulBound x y)
      (cfg (some (baseLabel 0)) v p op (true :: true :: code) (true :: true :: depth)
        (Encoding.encodeList encode (y :: x :: xs)) context)
      (cfg (some (baseLabel 0)) false false false code (true :: depth)
        (Encoding.encodeList encode ((x * y) :: xs)) context) := by
  obtain ⟨n, hn, ht⟩ := hmul x y xs code (true :: depth)
  have hs := ProgramLinking.relocate_trace mul (program add mul) id id mulLabel
    (some (baseLabel 0)) (cfg none false false false [] [] [] context)
    Function.injective_id Function.injective_id (program_mul_code add mul) ht
  simp only [ProgramLinking.embedCfg_id, ProgramLinking.relabelCfg,
    ProgramLinking.relocatePc, cfg] at hs
  have hc : Trace (program add mul) 1
      (cfg (some (baseLabel 17)) true true true code (true :: depth)
        (Encoding.encodeList encode (y :: x :: xs)) context)
      (cfg (some (mulLabel mul.entry)) true true true code (true :: depth)
        (Encoding.encodeList encode (y :: x :: xs)) context) :=
    .cons (mul_call_step add mul context code _ _) (.refl _)
  have hp := binary_prepare_trace add mul context true code
    (Encoding.encodeList encode (y :: x :: xs)) depth v p op
  have h := (hp.trans hc).trans hs
  refine ⟨13 + 1 + n, by omega, ?_⟩
  exact h

/-- Costs are the proven literal trace and actual arithmetic-service bounds,
plus the thirteen dispatcher transitions and one service-call jump. -/
def costs : Algorithm.OperationCosts R where
  load x := 11 * (encode x).length + 17
  add x y := 14 + addBound x y
  mul x y := 14 + mulBound x y

omit [Add R] [Mul R] in
theorem serializeCode_append (is js : List (Algorithm.Instr R)) :
    serializeCode encode (is ++ js) = serializeCode encode is ++ serializeCode encode js := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [serializeCode, ih, List.append_assoc]

include hadd hmul in
/-- The loop invariant includes the untouched code suffix, the complete operand
list, matching unary depth, and the unchanged arithmetic context. -/
theorem compile_runsIn (e : Algorithm.Expr R) (suffix : List (Algorithm.Instr R))
    (xs : List R) (v p op : Bool) :
    ∃ v' p' op', RunsIn (program add mul) (e.cost (costs encode addBound mulBound))
      (cfg (some (baseLabel 0)) v p op (serializeCode encode (e.compile ++ suffix))
        (operandDepth xs) (Encoding.encodeList encode xs) context)
      (cfg (some (baseLabel 0)) v' p' op' (serializeCode encode suffix)
        (operandDepth (e.eval :: xs)) (Encoding.encodeList encode (e.eval :: xs)) context) := by
  induction e generalizing suffix xs v p op with
  | lit x =>
      refine ⟨true, false, op, 11 * (encode x).length + 17, le_rfl, ?_⟩
      simpa [Algorithm.Expr.compile, Algorithm.Expr.eval, serializeCode, serializeInstr,
        operandDepth, Encoding.encodeList, List.replicate_succ] using
        push_trace add mul context (encode x) (serializeCode encode suffix)
          (operandDepth xs) (Encoding.encodeList encode xs) v p op
  | add e f he hf =>
      obtain ⟨ve, pe, oe, h₁⟩ := he (f.compile ++ .add :: suffix) xs v p op
      obtain ⟨vf, pf, of, h₂⟩ := hf (.add :: suffix) (e.eval :: xs) ve pe oe
      have h₃ := add_instruction add mul encode addBound context hadd e.eval f.eval xs
        (serializeCode encode suffix) (operandDepth xs) vf pf of
      refine ⟨false, false, false, ?_⟩
      simpa [Algorithm.Expr.compile, Algorithm.Expr.cost, Algorithm.Expr.eval, costs,
        List.append_assoc, serializeCode, serializeInstr, operandDepth, List.replicate_succ] using
        (h₁.trans h₂).trans h₃
  | mul e f he hf =>
      obtain ⟨ve, pe, oe, h₁⟩ := he (f.compile ++ .mul :: suffix) xs v p op
      obtain ⟨vf, pf, of, h₂⟩ := hf (.mul :: suffix) (e.eval :: xs) ve pe oe
      have h₃ := mul_instruction add mul encode mulBound context hmul e.eval f.eval xs
        (serializeCode encode suffix) (operandDepth xs) vf pf of
      refine ⟨false, false, false, ?_⟩
      simpa [Algorithm.Expr.compile, Algorithm.Expr.cost, Algorithm.Expr.eval, costs,
        List.append_assoc, serializeCode, serializeInstr, operandDepth, List.replicate_succ] using
        (h₁.trans h₂).trans h₃

include hadd hmul in
/-- Complete execution includes writing the initial list marker, all compiled
instructions, detecting EOF, and executing the actual halt. Arithmetic context
is supplied once and preserved. -/
theorem complete_runsIn (e : Algorithm.Expr R) :
    ∃ op, RunsIn (program add mul) (e.cost (costs encode addBound mulBound) + 5)
      (cfg (some (program add mul).entry) false false false (serializeCode encode e.compile)
        [] [] context)
      (cfg none false false op [] (operandDepth [e.eval])
        (Encoding.encodeList encode [e.eval]) context) := by
  obtain ⟨v, p, op, he⟩ := compile_runsIn add mul encode addBound mulBound context hadd hmul
    e [] [] false false false
  have he' : RunsIn (program add mul) (e.cost (costs encode addBound mulBound))
      (cfg (some (baseLabel 0)) false false false (serializeCode encode e.compile) [] [false] context)
      (cfg (some (baseLabel 0)) v p op [] (operandDepth [e.eval])
        (Encoding.encodeList encode [e.eval]) context) := by
    simpa only [List.append_nil, serializeCode, operandDepth, List.length_nil,
      List.replicate_zero, Encoding.encodeList] using he
  have hb : RunsIn (program add mul) 2
      (cfg (some (program add mul).entry) false false false (serializeCode encode e.compile) [] [] context)
      (cfg (some (baseLabel 0)) false false false (serializeCode encode e.compile) [] [false] context) :=
    ⟨2, le_rfl, boot_trace add mul context _⟩
  have hf : RunsIn (program add mul) 3
      (cfg (some (baseLabel 0)) v p op [] (operandDepth [e.eval])
        (Encoding.encodeList encode [e.eval]) context)
      (cfg none false false op [] (operandDepth [e.eval])
        (Encoding.encodeList encode [e.eval]) context) :=
    ⟨3, le_rfl, finish_trace add mul context _ _ v p op⟩
  refine ⟨op, ?_⟩
  convert (hb.trans he').trans hf using 1
  omega

end Execution

end SubexponentialSAT.SubexpPostfixInterpreter

end OAI.Algorithms
