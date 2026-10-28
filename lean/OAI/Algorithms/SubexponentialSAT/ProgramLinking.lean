import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BitProgram

namespace OAI.Algorithms

/-!
# Finite program relocation and linking

Every linked block is an instruction table inside one finite program.  A block's
halt can be replaced by a jump to a caller-specified continuation.  The proofs
below transfer actual instruction traces, including that final instruction, and
preserve all ambient registers and stacks outside the block's assigned ports.

The finite sizes and maps are fixed when the linked program is constructed; they
do not inspect the unbounded input stacks.
-/

namespace SubexponentialSAT.ProgramLinking

open BitProgram

variable {r s l R S L : ℕ}

/-- Relocate all finite references, optionally replacing halt by a return jump. -/
def relocateInstr (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) :
    Instr r s l → Instr R S L
  | .halt => match returnPc with | none => .halt | some pc => .goto pc
  | .goto next => .goto (label next)
  | .set dst value next => .set (register dst) value (label next)
  | .copy dst src next => .copy (register dst) (register src) (label next)
  | .bnot dst src next => .bnot (register dst) (register src) (label next)
  | .band dst left right next =>
      .band (register dst) (register left) (register right) (label next)
  | .bor dst left right next =>
      .bor (register dst) (register left) (register right) (label next)
  | .bxor dst left right next =>
      .bxor (register dst) (register left) (register right) (label next)
  | .branch test yes no => .branch (register test) (label yes) (label no)
  | .push port src next => .push (stack port) (register src) (label next)
  | .peek port value present next =>
      .peek (stack port) (register value) (register present) (label next)
  | .pop port value present next =>
      .pop (stack port) (register value) (register present) (label next)

def relocatePc (label : Fin l → Fin L) (returnPc : Option (Fin L)) :
    Option (Fin l) → Option (Fin L)
  | none => returnPc
  | some pc => some (label pc)

/-- A mathematical embedding into the caller's frame.  The executable program
does not evaluate this function: it uses the finite relocated instruction table. -/
noncomputable def embedCfg (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (c : Cfg r s l) : Cfg R S L where
  pc := relocatePc label returnPc c.pc
  regs := Function.extend register c.regs frame.regs
  «stacks» := Function.extend stack c.stacks frame.stacks

theorem extend_update {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    {f : α → β} (hf : Function.Injective f) (g : α → γ) (base : β → γ)
    (a : α) (value : γ) :
    Function.extend f (Function.update g a value) base =
      Function.update (Function.extend f g base) (f a) value := by
  classical
  funext b
  by_cases hb : ∃ a, f a = b
  · obtain ⟨x, rfl⟩ := hb
    simp only [hf.extend_apply, Function.update_apply, hf.eq_iff]
  · have hne : b ≠ f a := by
      intro h
      exact hb ⟨a, h.symm⟩
    simp only [Function.extend_apply' _ _ _ hb, Function.update_of_ne hne]

@[simp] theorem extend_id {α γ : Type*} (g base : α → γ) :
    Function.extend id g base = g := by
  funext a
  exact Function.injective_id.extend_apply g base a

@[simp] theorem embedCfg_register (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (label : Fin l → Fin L)
    (returnPc : Option (Fin L)) (frame : Cfg R S L) (c : Cfg r s l)
    (hinj : Function.Injective register) (a : Fin r) :
    (embedCfg register stack label returnPc frame c).regs (register a) = c.regs a :=
  hinj.extend_apply _ _ _

@[simp] theorem embedCfg_stack (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (label : Fin l → Fin L)
    (returnPc : Option (Fin L)) (frame : Cfg R S L) (c : Cfg r s l)
    (hinj : Function.Injective stack) (a : Fin s) :
    (embedCfg register stack label returnPc frame c).stacks (stack a) = c.stacks a :=
  hinj.extend_apply _ _ _

theorem embedCfg_register_frame (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (label : Fin l → Fin L)
    (returnPc : Option (Fin L)) (frame : Cfg R S L) (c : Cfg r s l)
    (a : Fin R) (ha : ¬ ∃ b, register b = a) :
    (embedCfg register stack label returnPc frame c).regs a = frame.regs a :=
  Function.extend_apply' _ _ _ ha

theorem embedCfg_stack_frame (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (label : Fin l → Fin L)
    (returnPc : Option (Fin L)) (frame : Cfg R S L) (c : Cfg r s l)
    (a : Fin S) (ha : ¬ ∃ b, stack b = a) :
    (embedCfg register stack label returnPc frame c).stacks a = frame.stacks a :=
  Function.extend_apply' _ _ _ ha

/-- Relocation commutes with every instruction, even when read value/presence
registers alias.  Injective port maps preserve exactly the source aliases. -/
theorem execInstr_relocate (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (instr : Instr r s l) (c : Cfg r s l) :
    execInstr (relocateInstr register stack label returnPc instr)
        (embedCfg register stack label returnPc frame c) =
      embedCfg register stack label returnPc frame (execInstr instr c) := by
  cases instr <;> cases returnPc <;>
    simp [relocateInstr, execInstr, embedCfg, relocatePc, readRegs,
      hregister.extend_apply, hstack.extend_apply,
      extend_update hregister, extend_update hstack, apply_ite]
  all_goals split <;> simp_all

/-- Code agreement is an ordinary equality of actual finite table entries. -/
abbrev CodeEmbedding (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) : Prop :=
  ∀ pc, q.code (label pc) = relocateInstr register stack label returnPc (p.code pc)

theorem relocate_step_at (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    {c c' : Cfg r s l}
    (hcode : ∀ pc, c.pc = some pc →
      q.code (label pc) = relocateInstr register stack label returnPc (p.code pc))
    (hstep : step p c = some c') :
    step q (embedCfg register stack label returnPc frame c) =
      some (embedCfg register stack label returnPc frame c') := by
  cases hpc : c.pc with
  | none => simp [step, hpc] at hstep
  | some pc =>
      have hc' : execInstr (p.code pc) c = c' := by
        simpa [step, hpc] using hstep
      simp only [step, embedCfg, hpc, relocatePc, Option.map_some]
      rw [hcode pc hpc]
      change some (execInstr (relocateInstr register stack label returnPc (p.code pc))
        (embedCfg register stack label returnPc frame c)) = _
      rw [execInstr_relocate register stack label returnPc frame hregister hstack, hc']
      rfl

theorem relocate_step (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : CodeEmbedding p q register stack label returnPc)
    {c c' : Cfg r s l} (hstep : step p c = some c') :
    step q (embedCfg register stack label returnPc frame c) =
      some (embedCfg register stack label returnPc frame c') :=
  relocate_step_at p q register stack label returnPc frame hregister hstack
    (fun pc _ => hcode pc) hstep

/-- Complete block traces transfer with exactly the same number of steps.
In particular a source halt is the target's actual return-jump instruction. -/
theorem relocate_trace (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : CodeEmbedding p q register stack label returnPc)
    {steps : ℕ} {c c' : Cfg r s l} (htrace : Trace p steps c c') :
    Trace q steps (embedCfg register stack label returnPc frame c)
      (embedCfg register stack label returnPc frame c') := by
  induction htrace with
  | refl c => exact .refl _
  | cons hs ht ih =>
      exact .cons
        (relocate_step p q register stack label returnPc frame hregister hstack hcode hs) ih

theorem relocate_runsIn (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : CodeEmbedding p q register stack label returnPc)
    {bound : ℕ} {c c' : Cfg r s l} (htrace : RunsIn p bound c c') :
    RunsIn q bound (embedCfg register stack label returnPc frame c)
      (embedCfg register stack label returnPc frame c') := by
  obtain ⟨steps, hsteps, ht⟩ := htrace
  exact ⟨steps, hsteps,
    relocate_trace p q register stack label returnPc frame hregister hstack hcode ht⟩

/-- Install a standalone program on a larger port set, keeping its labels. -/
abbrev liftProgram (p : Program r s l) (register : Fin r → Fin R)
    (stack : Fin s → Fin S) : Program R S l where
  inputStack := stack p.inputStack
  outputStack := stack p.outputStack
  entry := p.entry
  code := fun pc => relocateInstr register stack id none (p.code pc)

theorem liftProgram_trace (p : Program r s l) (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (frame : Cfg R S l)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    {n : ℕ} {a b : Cfg r s l} (h : Trace p n a b) :
    Trace (liftProgram p register stack) n
      (embedCfg register stack id none frame a) (embedCfg register stack id none frame b) :=
  relocate_trace p _ register stack id none frame hregister hstack (fun _ => rfl) h

theorem liftProgram_runsIn (p : Program r s l) (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (frame : Cfg R S l)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    {n : ℕ} {a b : Cfg r s l} (h : RunsIn p n a b) :
    RunsIn (liftProgram p register stack) n
      (embedCfg register stack id none frame a) (embedCfg register stack id none frame b) :=
  relocate_runsIn p _ register stack id none frame hregister hstack (fun _ => rfl) h

theorem trace_from_halted (p : Program r s l) {n : ℕ} {a b : Cfg r s l}
    (h : Trace p n a b) (ha : a.pc = none) : b.pc = none := by
  cases h with
  | refl => exact ha
  | cons hs _ => simp [step, ha] at hs

/-- A trace ending at an active label has not executed any halt instruction.
Thus the target may give all source halt labels an arbitrary continuation body. -/
theorem relocate_trace_before_halt (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : ∀ pc, p.code pc ≠ .halt →
      q.code (label pc) = relocateInstr register stack label returnPc (p.code pc))
    {n : ℕ} {a b : Cfg r s l} (h : Trace p n a b) (hb : b.pc ≠ none) :
    Trace q n (embedCfg register stack label returnPc frame a)
      (embedCfg register stack label returnPc frame b) := by
  induction h with
  | refl => exact .refl _
  | @cons n a c b hs ht ih =>
      have hlocal : ∀ pc, a.pc = some pc →
          q.code (label pc) = relocateInstr register stack label returnPc (p.code pc) := by
        intro pc hpc
        apply hcode pc
        intro hhalt
        have hc : c = execInstr .halt a := by
          simpa [step, hpc, hhalt] using hs.symm
        have hcpc : c.pc = none := by simp [hc, execInstr]
        exact hb (trace_from_halted p ht hcpc)
      exact .cons
        (relocate_step_at p q register stack label returnPc frame hregister hstack hlocal hs)
        (ih hb)

/-- Designated-exit version: the exit's instruction can be replaced without
charging a step until the caller actually executes that instruction. -/
theorem relocate_trace_to_exit (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (exit : Fin l) (hexit : p.code exit = .halt)
    (hcode : ∀ pc, pc ≠ exit →
      q.code (label pc) = relocateInstr register stack label returnPc (p.code pc))
    {n : ℕ} {a b : Cfg r s l} (h : Trace p n a b) (hb : b.pc = some exit) :
    Trace q n (embedCfg register stack label returnPc frame a)
      (embedCfg register stack label returnPc frame b) := by
  apply relocate_trace_before_halt p q register stack label returnPc frame
    hregister hstack ?_ h (by simp [hb])
  intro pc hpc
  apply hcode pc
  intro heq
  exact hpc (heq ▸ hexit)

/-! ## Concrete disjoint linking -/

/-- Install two finite tables in disjoint label ranges.  The first block's halts
jump to the second block's entry; the second block's halts stop the program.
Register and stack assignments can share ports between the two blocks. -/
abbrev linkInto {r' s' m : ℕ} (p : Program r s l) (q : Program r' s' m)
    (registerP : Fin r → Fin R) (stackP : Fin s → Fin S)
    (registerQ : Fin r' → Fin R) (stackQ : Fin s' → Fin S) :
    Program R S (l + m) where
  inputStack := stackP p.inputStack
  outputStack := stackQ q.outputStack
  entry := Fin.castAdd m p.entry
  code := Fin.addCases
    (fun pc => relocateInstr registerP stackP (Fin.castAdd m)
      (some (Fin.natAdd l q.entry)) (p.code pc))
    (fun pc => relocateInstr registerQ stackQ (Fin.natAdd l) none (q.code pc))

theorem linkInto_leftCode {r' s' m : ℕ} (p : Program r s l) (q : Program r' s' m)
    (registerP : Fin r → Fin R) (stackP : Fin s → Fin S)
    (registerQ : Fin r' → Fin R) (stackQ : Fin s' → Fin S) :
    CodeEmbedding p (linkInto p q registerP stackP registerQ stackQ)
      registerP stackP (Fin.castAdd m) (some (Fin.natAdd l q.entry)) := by
  intro pc
  simp []

theorem linkInto_rightCode {r' s' m : ℕ} (p : Program r s l) (q : Program r' s' m)
    (registerP : Fin r → Fin R) (stackP : Fin s → Fin S)
    (registerQ : Fin r' → Fin R) (stackQ : Fin s' → Fin S) :
    CodeEmbedding q (linkInto p q registerP stackP registerQ stackQ)
      registerQ stackQ (Fin.natAdd l) none := by
  intro pc
  simp []

/-- Linking with port assignments uses a checked equality at the shared data
boundary.  Both source traces execute inside the concrete table above. -/
theorem linkInto_trace {r' s' m : ℕ} (p : Program r s l) (q : Program r' s' m)
    (registerP : Fin r → Fin R) (stackP : Fin s → Fin S)
    (registerQ : Fin r' → Fin R) (stackQ : Fin s' → Fin S)
    (hregisterP : Function.Injective registerP) (hstackP : Function.Injective stackP)
    (hregisterQ : Function.Injective registerQ) (hstackQ : Function.Injective stackQ)
    (frameP frameQ : Cfg R S (l + m)) {n₁ n₂ : ℕ}
    {a b : Cfg r s l} {c d : Cfg r' s' m}
    (hp : Trace p n₁ a b) (hq : Trace q n₂ c d)
    (boundary : embedCfg registerP stackP (Fin.castAdd m)
        (some (Fin.natAdd l q.entry)) frameP b =
      embedCfg registerQ stackQ (Fin.natAdd l) none frameQ c) :
    Trace (linkInto p q registerP stackP registerQ stackQ) (n₁ + n₂)
      (embedCfg registerP stackP (Fin.castAdd m)
        (some (Fin.natAdd l q.entry)) frameP a)
      (embedCfg registerQ stackQ (Fin.natAdd l) none frameQ d) := by
  have hp' := relocate_trace p _ registerP stackP (Fin.castAdd m)
    (some (Fin.natAdd l q.entry)) frameP hregisterP hstackP
    (linkInto_leftCode p q registerP stackP registerQ stackQ) hp
  have hq' := relocate_trace q _ registerQ stackQ (Fin.natAdd l) none
    frameQ hregisterQ hstackQ
    (linkInto_rightCode p q registerP stackP registerQ stackQ) hq
  rw [boundary] at hp'
  exact hp'.trans hq'

/-- Only change the finite program counter, keeping all data verbatim. -/
abbrev relabelCfg (label : Fin l → Fin L) (returnPc : Option (Fin L))
    (c : Cfg r s l) : Cfg r s L where
  pc := relocatePc label returnPc c.pc
  regs := c.regs
  «stacks» := c.stacks

@[simp] theorem embedCfg_id (label : Fin l → Fin L) (returnPc : Option (Fin L))
    (frame : Cfg r s L) (c : Cfg r s l) :
    embedCfg id id label returnPc frame c = relabelCfg label returnPc c := by
  simp [embedCfg, relabelCfg]

/-- Start another finite table with the current register and stack contents. -/
abbrev enter {m : ℕ} (q : Program r s m) (c : Cfg r s l) : Cfg r s m where
  pc := some q.entry
  regs := c.regs
  «stacks» := c.stacks

/-- Sequential composition when both blocks already use the same port set. -/
abbrev link {m : ℕ} (p : Program r s l) (q : Program r s m) : Program r s (l + m) :=
  linkInto p q id id id id

@[simp] theorem link_initial {m : ℕ} (p : Program r s l) (q : Program r s m)
    (input : List Bool) :
    relabelCfg (Fin.castAdd m) (some (Fin.natAdd l q.entry)) (initial p input) =
      initial (link p q) input := rfl

@[simp] theorem link_terminal {m : ℕ} (p : Program r s l) (q : Program r s m)
    (output : List Bool) :
    relabelCfg (Fin.natAdd l) none (terminal q output) =
      terminal (link p q) output := rfl

theorem link_left_trace {m : ℕ} (p : Program r s l) (q : Program r s m)
    {n : ℕ} {a b : Cfg r s l} (h : Trace p n a b) :
    Trace (link p q) n
      (relabelCfg (Fin.castAdd m) (some (Fin.natAdd l q.entry)) a)
      (relabelCfg (Fin.castAdd m) (some (Fin.natAdd l q.entry)) b) := by
  let frame := relabelCfg (Fin.castAdd m) (some (Fin.natAdd l q.entry)) a
  simpa only [embedCfg_id] using
    relocate_trace p (link p q) id id (Fin.castAdd m)
      (some (Fin.natAdd l q.entry)) frame Function.injective_id Function.injective_id
      (linkInto_leftCode p q id id id id) h

theorem link_right_trace {m : ℕ} (p : Program r s l) (q : Program r s m)
    {n : ℕ} {a b : Cfg r s m} (h : Trace q n a b) :
    Trace (link p q) n
      (relabelCfg (Fin.natAdd l) none a) (relabelCfg (Fin.natAdd l) none b) := by
  let frame := relabelCfg (Fin.natAdd l) none a
  simpa only [embedCfg_id] using
    relocate_trace q (link p q) id id (Fin.natAdd l) none frame
      Function.injective_id Function.injective_id (linkInto_rightCode p q id id id id) h

/-- No dispatcher or subroutine oracle is added: the replaced halt itself is
the one-step return jump, so the composed trace length is exactly the sum. -/
theorem link_trace {m : ℕ} (p : Program r s l) (q : Program r s m)
    {n₁ n₂ : ℕ} {a b : Cfg r s l} {c : Cfg r s m}
    (hp : Trace p n₁ a b) (hb : b.pc = none)
    (hq : Trace q n₂ (enter q b) c) :
    Trace (link p q) (n₁ + n₂)
      (relabelCfg (Fin.castAdd m) (some (Fin.natAdd l q.entry)) a)
      (relabelCfg (Fin.natAdd l) none c) := by
  have boundary : relabelCfg (Fin.castAdd m) (some (Fin.natAdd l q.entry)) b =
      relabelCfg (Fin.natAdd l) none (enter q b) := by
    simp [relabelCfg, relocatePc, hb]
  have hp' := link_left_trace p q hp
  rw [boundary] at hp'
  exact hp'.trans (link_right_trace p q hq)

theorem link_runsIn {m : ℕ} (p : Program r s l) (q : Program r s m)
    {n₁ n₂ : ℕ} {a b : Cfg r s l} {c : Cfg r s m}
    (hp : RunsIn p n₁ a b) (hb : b.pc = none)
    (hq : RunsIn q n₂ (enter q b) c) :
    RunsIn (link p q) (n₁ + n₂)
      (relabelCfg (Fin.castAdd m) (some (Fin.natAdd l q.entry)) a)
      (relabelCfg (Fin.natAdd l) none c) := by
  obtain ⟨i, hi, hpi⟩ := hp
  obtain ⟨j, hj, hqj⟩ := hq
  exact ⟨i + j, Nat.add_le_add hi hj, link_trace p q hpi hb hqj⟩

/-- End-to-end sequential execution from raw program input to canonical output.
The second routine starts with the first routine's actual data, not a reset. -/
theorem link_complete_trace {m : ℕ} (p : Program r s l) (q : Program r s m)
    (input output : List Bool) {n₁ n₂ : ℕ} {b : Cfg r s l}
    (hp : Trace p n₁ (initial p input) b) (hb : b.pc = none)
    (hq : Trace q n₂ (enter q b) (terminal q output)) :
    Trace (link p q) (n₁ + n₂) (initial (link p q) input) (terminal (link p q) output) := by
  rw [← link_initial p q input, ← link_terminal p q output]
  exact link_trace p q hp hb hq

theorem link_complete_runsIn {m : ℕ} (p : Program r s l) (q : Program r s m)
    (input output : List Bool) {n₁ n₂ : ℕ} {b : Cfg r s l}
    (hp : RunsIn p n₁ (initial p input) b) (hb : b.pc = none)
    (hq : RunsIn q n₂ (enter q b) (terminal q output)) :
    RunsIn (link p q) (n₁ + n₂) (initial (link p q) input) (terminal (link p q) output) := by
  rw [← link_initial p q input, ← link_terminal p q output]
  exact link_runsIn p q hp hb hq

end SubexponentialSAT.ProgramLinking

end OAI.Algorithms
