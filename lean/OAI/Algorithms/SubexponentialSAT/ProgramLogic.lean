import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Computation
import OAI.Algorithms.SubexponentialSAT.BitProgram

namespace OAI.Algorithms

/-!
# Measured verification rules for fixed bit programs

Every execution judgment below contains actual transitions of one fixed step
function. Loop iterations may be controlled by unbounded data; neither the
transition function nor its finite control changes with the iteration count.
No judgment assigns a cost to an unimplemented mathematical function.
-/

namespace SubexponentialSAT.ProgramLogic

open SubexponentialSAT.Computation
open scoped BigOperators

section Traces

variable {Cfg : Type} {step : Cfg → Option Cfg}

/-- Cut an actual trace at a specified step index. -/
theorem trace_cut {steps : ℕ} {a c : Cfg} (h : Trace step steps a c)
    (cutIdx : ℕ) (hp : cutIdx ≤ steps) :
    ∃ b, Trace step cutIdx a b ∧ Trace step (steps - cutIdx) b c := by
  induction h generalizing cutIdx with
  | refl a =>
      have hz : cutIdx = 0 := by omega
      subst cutIdx
      exact ⟨a, Trace.refl a, Trace.refl a⟩
  | @cons n a d c hs ht ih =>
      cases cutIdx with
      | zero => exact ⟨a, Trace.refl a, by simpa using Trace.cons hs ht⟩
      | succ cutIdx =>
          obtain ⟨b, hab, hbc⟩ := ih cutIdx (by omega)
          exact ⟨b, Trace.cons hs hab, by simpa using hbc⟩

/-- An inductive configuration invariant holds throughout any actual trace. -/
theorem invariant_trace (I : Cfg → Prop)
    (preserve : ∀ a b, I a → step a = some b → I b)
    {steps : ℕ} {a b : Cfg} (h : Trace step steps a b) (ha : I a) : I b := by
  induction h with
  | refl => exact ha
  | cons hs ht ih => exact ih (preserve _ _ ha hs)

/-- A frame observation preserved by each actual step is preserved by the run. -/
theorem frame_trace {Frame : Type} (frame : Cfg → Frame)
    (preserve : ∀ a b, step a = some b → frame b = frame a)
    {steps : ℕ} {a b : Cfg} (h : Trace step steps a b) : frame b = frame a := by
  induction h with
  | refl => rfl
  | cons hs ht ih => exact ih.trans (preserve _ _ hs)

end Traces

/-- A relational, input-dependent measured specification for one fixed program.
Its postcondition may refer to both the initial and final configurations. -/
def Spec {Cfg : Type} (step : Cfg → Option Cfg) (pre : Cfg → Prop)
    (post : Cfg → Cfg → Prop) (bound : Cfg → ℕ) : Prop :=
  ∀ a, pre a → ∃ b, RunsIn step (bound a) a b ∧ post a b

namespace Spec

variable {Cfg : Type} {step : Cfg → Option Cfg}

/-- A specified actual instruction establishes a one-step specification. -/
theorem instruction {pre : Cfg → Prop} (next : Cfg → Cfg)
    (table : ∀ a, pre a → step a = some (next a)) :
    Spec step pre (fun a b => b = next a) (fun _ => 1) := by
  intro a ha
  exact ⟨next a, ⟨1, le_rfl, Trace.cons (table a ha) (Trace.refl _)⟩, rfl⟩

theorem skip (pre : Cfg → Prop) :
    Spec step pre (fun a b => b = a) (fun _ => 0) := by
  intro a _
  exact ⟨a, RunsIn.refl step a, rfl⟩

/-- Strengthen the input condition, weaken the relational output condition,
and enlarge a bound already proved for actual executions. -/
theorem consequence {pre pre' : Cfg → Prop} {post post' : Cfg → Cfg → Prop}
    {bound bound' : Cfg → ℕ}
    (h : Spec step pre post bound)
    (hin : ∀ a, pre' a → pre a)
    (hout : ∀ a b, pre' a → post a b → post' a b)
    (htime : ∀ a, pre' a → bound a ≤ bound' a) :
    Spec step pre' post' bound' := by
  intro a ha
  obtain ⟨b, hrun, hpost⟩ := h a (hin a ha)
  exact ⟨b, hrun.mono (htime a ha), hout a b ha hpost⟩

/-- Compose two measured blocks on the same concrete transition function.
The second block's bound is bounded in terms of the original input. -/
theorem sequence {pre middle : Cfg → Prop} {post₁ post₂ : Cfg → Cfg → Prop}
    {bound₁ bound₂ extra : Cfg → ℕ}
    (first : Spec step pre post₁ bound₁)
    (second : Spec step middle post₂ bound₂)
    (ready : ∀ a b, pre a → post₁ a b → middle b)
    (extra_bound : ∀ a b, pre a → post₁ a b → bound₂ b ≤ extra a) :
    Spec step pre
      (fun a c => ∃ b, post₁ a b ∧ post₂ b c)
      (fun a => bound₁ a + extra a) := by
  intro a ha
  obtain ⟨b, hab, hpab⟩ := first a ha
  obtain ⟨c, hbc, hpbc⟩ := second b (ready a b ha hpab)
  exact ⟨c, (hab.trans hbc).mono (Nat.add_le_add_left (extra_bound a b ha hpab) _),
    b, hpab, hpbc⟩

/-- Branching on an initial-state predicate combines existing measured proofs;
a concrete guard instruction must be included in the branch specifications. -/
theorem cases {pre : Cfg → Prop} {post : Cfg → Cfg → Prop}
    {bound : Cfg → ℕ} (test : Cfg → Prop)
    (yes : Spec step (fun a => pre a ∧ test a) post bound)
    (no : Spec step (fun a => pre a ∧ ¬ test a) post bound) :
    Spec step pre post bound := by
  classical
  intro a ha
  by_cases ht : test a
  · exact yes a ⟨ha, ht⟩
  · exact no a ⟨ha, ht⟩

/-- Preserve a frame alongside a proved specification. -/
theorem frame {pre : Cfg → Prop} {post : Cfg → Cfg → Prop} {bound : Cfg → ℕ}
    {Frame : Type} (observe : Cfg → Frame)
    (preserve : ∀ a b, step a = some b → observe b = observe a)
    (h : Spec step pre post bound) :
    Spec step pre (fun a b => post a b ∧ observe b = observe a) bound := by
  intro a ha
  obtain ⟨b, ⟨steps, hsteps, htrace⟩, hpost⟩ := h a ha
  exact ⟨b, ⟨steps, hsteps, htrace⟩, hpost, frame_trace observe preserve htrace⟩

end Spec

section Loops

variable {Cfg : Type} {step : Cfg → Option Cfg}

/-- Total execution of a countdown loop, with the sum of the actual
per-iteration bounds and a separately charged exit block. The invariant may
relate the natural index to a binary counter in unbounded program storage. -/
theorem countdown (I : ℕ → Cfg → Prop) (done : Cfg → Prop)
    (bodyCost : ℕ → ℕ) (exitCost : ℕ)
    (exit : ∀ a, I 0 a → ∃ b, RunsIn step exitCost a b ∧ done b)
    (body : ∀ n a, I (n + 1) a →
      ∃ b, RunsIn step (bodyCost n) a b ∧ I n b) :
    ∀ n a, I n a → ∃ b,
      RunsIn step ((∑ i ∈ Finset.range n, bodyCost i) + exitCost) a b ∧ done b := by
  intro n
  induction n with
  | zero =>
      intro a ha
      simpa using exit a ha
  | succ n ih =>
      intro a ha
      obtain ⟨mid, hbody, hmid⟩ := body n a ha
      obtain ⟨b, hrest, hdone⟩ := ih mid hmid
      refine ⟨b, ?_, hdone⟩
      simpa [Finset.sum_range_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hbody.trans hrest

/-- A uniform body bound yields the usual linear-in-iteration-count budget,
without putting that iteration count in finite control. -/
theorem countdown_uniform (I : ℕ → Cfg → Prop) (done : Cfg → Prop)
    (bodyCost exitCost : ℕ)
    (exit : ∀ a, I 0 a → ∃ b, RunsIn step exitCost a b ∧ done b)
    (body : ∀ n a, I (n + 1) a →
      ∃ b, RunsIn step bodyCost a b ∧ I n b) :
    ∀ n a, I n a → ∃ b,
      RunsIn step (n * bodyCost + exitCost) a b ∧ done b := by
  intro n a ha
  simpa using countdown I done (fun _ => bodyCost) exitCost exit body n a ha

/-- A while-loop variant may decrease by more than one. Each loop traversal
and the final exit must be proved using the same actual step function. -/
theorem while_variant (I : Cfg → Prop) (guard : Cfg → Bool) (variant : Cfg → ℕ)
    (done : Cfg → Prop) (bodyCost exitCost : ℕ)
    (exit : ∀ a, I a → guard a = false →
      ∃ b, RunsIn step exitCost a b ∧ done b)
    (body : ∀ a, I a → guard a = true →
      ∃ b, RunsIn step bodyCost a b ∧ I b ∧ variant b < variant a) :
    ∀ fuel a, I a → variant a ≤ fuel → ∃ b,
      RunsIn step (fuel * bodyCost + exitCost) a b ∧ done b := by
  intro fuel
  induction fuel with
  | zero =>
      intro a ha hvar
      cases hg : guard a with
      | false => simpa using exit a ha hg
      | true =>
          obtain ⟨b, _, _, hlt⟩ := body a ha hg
          omega
  | succ fuel ih =>
      intro a ha hvar
      cases hg : guard a with
      | false =>
          obtain ⟨b, hrun, hdone⟩ := exit a ha hg
          exact ⟨b, hrun.mono (by omega), hdone⟩
      | true =>
          obtain ⟨mid, hbody, hmid, hlt⟩ := body a ha hg
          obtain ⟨b, hrest, hdone⟩ := ih mid hmid (by omega)
          refine ⟨b, (hbody.trans hrest).mono ?_, hdone⟩
          simp only [Nat.add_mul, Nat.one_mul]
          omega

end Loops

section BitPrograms

open SubexponentialSAT.BitProgram

variable {r s l : ℕ}

/-- Registers possibly modified by this concrete instruction. -/
def registerWrites : Instr r s l → Finset (Fin r)
  | .set dst _ _ => {dst}
  | .copy dst _ _ => {dst}
  | .bnot dst _ _ => {dst}
  | .band dst _ _ _ => {dst}
  | .bor dst _ _ _ => {dst}
  | .bxor dst _ _ _ => {dst}
  | .peek _ value present _ => {value, present}
  | .pop _ value present _ => {value, present}
  | _ => ∅

/-- Stacks possibly modified by this concrete instruction. Peeking is read-only. -/
def stackWrites : Instr r s l → Finset (Fin s)
  | .push stack _ _ => {stack}
  | .pop stack _ _ _ => {stack}
  | _ => ∅

theorem execInstr_register_frame (instr : Instr r s l) (c : Cfg r s l) (k : Fin r)
    (hk : k ∉ registerWrites instr) : (execInstr instr c).regs k = c.regs k := by
  cases instr <;> simp_all [registerWrites, execInstr, readRegs]

theorem execInstr_stack_frame (instr : Instr r s l) (c : Cfg r s l) (k : Fin s)
    (hk : k ∉ stackWrites instr) : (execInstr instr c).stacks k = c.stacks k := by
  cases instr <;> simp_all [stackWrites, execInstr]

theorem step_register_frame (p : Program r s l) {a b : Cfg r s l} (k : Fin r)
    (safe : ∀ label, a.pc = some label → k ∉ registerWrites (p.code label))
    (hs : step p a = some b) : b.regs k = a.regs k := by
  cases hp : a.pc with
  | none => simp [step, hp] at hs
  | some label =>
      have heq : execInstr (p.code label) a = b := by simpa [step, hp] using hs
      subst b
      exact execInstr_register_frame _ _ _ (safe label hp)

theorem step_stack_frame (p : Program r s l) {a b : Cfg r s l} (k : Fin s)
    (safe : ∀ label, a.pc = some label → k ∉ stackWrites (p.code label))
    (hs : step p a = some b) : b.stacks k = a.stacks k := by
  cases hp : a.pc with
  | none => simp [step, hp] at hs
  | some label =>
      have heq : execInstr (p.code label) a = b := by simpa [step, hp] using hs
      subst b
      exact execInstr_stack_frame _ _ _ (safe label hp)

/-- Every transition is still a transition of p; region membership records only
the instruction addresses executed before the final boundary is reached. -/
inductive RegionTrace (p : Program r s l) (region : Finset (Fin l)) :
    ℕ → Cfg r s l → Cfg r s l → Prop
  | refl (a) : RegionTrace p region 0 a a
  | cons {n a b c label} : a.pc = some label → label ∈ region →
      step p a = some b → RegionTrace p region n b c → RegionTrace p region (n + 1) a c

namespace RegionTrace

variable {p : Program r s l} {region : Finset (Fin l)}

theorem to_trace {n : ℕ} {a b : Cfg r s l} (h : RegionTrace p region n a b) :
    SubexponentialSAT.Computation.Trace (step p) n a b := by
  induction h with
  | refl => exact .refl _
  | cons _ _ hs _ ih => exact .cons hs ih

theorem trans {n m : ℕ} {a b c : Cfg r s l}
    (first : RegionTrace p region n a b) (second : RegionTrace p region m b c) :
    RegionTrace p region (n + m) a c := by
  induction first with
  | refl => simpa using second
  | cons hpc hmem hs ht ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        RegionTrace.cons hpc hmem hs (ih second)

theorem mono {region' : Finset (Fin l)} (hsub : region ⊆ region')
    {n : ℕ} {a b : Cfg r s l} (h : RegionTrace p region n a b) :
    RegionTrace p region' n a b := by
  induction h with
  | refl => exact .refl _
  | cons hpc hmem hs ht ih => exact .cons hpc (hsub hmem) hs ih

theorem register_frame {n : ℕ} {a b : Cfg r s l}
    (h : RegionTrace p region n a b) (k : Fin r)
    (safe : ∀ label ∈ region, k ∉ registerWrites (p.code label)) :
    b.regs k = a.regs k := by
  induction h with
  | refl => rfl
  | @cons n a mid b label hpc hmem hs ht ih =>
      apply ih.trans
      apply step_register_frame p k _ hs
      intro label' hpc'
      have heq : label' = label := Option.some.inj (hpc'.symm.trans hpc)
      subst label'
      exact safe label hmem

theorem stack_frame {n : ℕ} {a b : Cfg r s l}
    (h : RegionTrace p region n a b) (k : Fin s)
    (safe : ∀ label ∈ region, k ∉ stackWrites (p.code label)) :
    b.stacks k = a.stacks k := by
  induction h with
  | refl => rfl
  | @cons n a mid b label hpc hmem hs ht ih =>
      apply ih.trans
      apply step_stack_frame p k _ hs
      intro label' hpc'
      have heq : label' = label := Option.some.inj (hpc'.symm.trans hpc)
      subst label'
      exact safe label hmem

end RegionTrace

/-- An active block entry and an explicit active-or-halted exit boundary.
The final boundary instruction is not executed by this specification. -/
abbrev Block (p : Program r s l) (entry : Fin l) (exit : Option (Fin l))
    (pre : Cfg r s l → Prop) (post : Cfg r s l → Cfg r s l → Prop)
    (bound : Cfg r s l → ℕ) : Prop :=
  Spec (step p) (fun a => a.pc = some entry ∧ pre a)
    (fun a b => b.pc = exit ∧ post a b) bound

namespace Block

theorem instruction (p : Program r s l) (entry : Fin l) (exit : Option (Fin l))
    (instr : Instr r s l) (pre : Cfg r s l → Prop)
    (code : p.code entry = instr)
    (destination : ∀ a, pre a → (execInstr instr a).pc = exit) :
    Block p entry exit pre (fun a b => b = execInstr instr a) (fun _ => 1) := by
  intro a ha
  exact ⟨execInstr instr a,
    ⟨1, le_rfl, .cons (step_code p a entry instr ha.1 code) (.refl _)⟩,
    destination a ha.2, rfl⟩

theorem sequence (p : Program r s l) {entry middle : Fin l} {exit : Option (Fin l)}
    {pre midPre : Cfg r s l → Prop}
    {post₁ post₂ : Cfg r s l → Cfg r s l → Prop}
    {bound₁ bound₂ extra : Cfg r s l → ℕ}
    (first : Block p entry (some middle) pre post₁ bound₁)
    (second : Block p middle exit midPre post₂ bound₂)
    (ready : ∀ a b, pre a → post₁ a b → midPre b)
    (time : ∀ a b, pre a → post₁ a b → bound₂ b ≤ extra a) :
    Block p entry exit pre (fun a c => ∃ b, post₁ a b ∧ post₂ b c)
      (fun a => bound₁ a + extra a) := by
  intro a ha
  obtain ⟨b, hab, hpc, hpab⟩ := first a ha
  obtain ⟨c, hbc, hexit, hpbc⟩ := second b ⟨hpc, ready a b ha.2 hpab⟩
  exact ⟨c, (hab.trans hbc).mono (Nat.add_le_add_left (time a b ha.2 hpab) _),
    hexit, b, hpab, hpbc⟩

/-- A loop body returns to the same concrete header. Its decreasing index is
assertion data, not an additional control label or register type. -/
theorem countdown (p : Program r s l) (header : Fin l) (exitLabel : Option (Fin l))
    (I : ℕ → Cfg r s l → Prop) (done : Cfg r s l → Prop)
    (bodyCost : ℕ → ℕ) (exitCost : ℕ)
    (exit : ∀ a, a.pc = some header → I 0 a →
      ∃ b, RunsIn p exitCost a b ∧ b.pc = exitLabel ∧ done b)
    (body : ∀ n a, a.pc = some header → I (n + 1) a →
      ∃ b, RunsIn p (bodyCost n) a b ∧ b.pc = some header ∧ I n b) :
    ∀ n, Block p header exitLabel (I n) (fun _ b => done b)
      (fun _ => (∑ i ∈ Finset.range n, bodyCost i) + exitCost) := by
  intro n a ha
  exact SubexponentialSAT.ProgramLogic.countdown
    (fun n c => c.pc = some header ∧ I n c)
    (fun c => c.pc = exitLabel ∧ done c) bodyCost exitCost
    (fun c hc => exit c hc.1 hc.2)
    (fun n c hc => body n c hc.1 hc.2) n a ha

/-- The data-dependent while rule specialized to one concrete program header.
Branch tests and back edges must be included in the supplied measured blocks. -/
theorem while_variant (p : Program r s l) (header : Fin l) (exitLabel : Option (Fin l))
    (I : Cfg r s l → Prop) (guard : Cfg r s l → Bool)
    (variant : Cfg r s l → ℕ) (done : Cfg r s l → Prop)
    (bodyCost exitCost : ℕ)
    (exit : ∀ a, a.pc = some header → I a → guard a = false →
      ∃ b, RunsIn p exitCost a b ∧ b.pc = exitLabel ∧ done b)
    (body : ∀ a, a.pc = some header → I a → guard a = true →
      ∃ b, RunsIn p bodyCost a b ∧ b.pc = some header ∧ I b ∧ variant b < variant a) :
    ∀ fuel, Block p header exitLabel (fun a => I a ∧ variant a ≤ fuel)
      (fun _ b => done b) (fun _ => fuel * bodyCost + exitCost) := by
  intro fuel a ha
  exact SubexponentialSAT.ProgramLogic.while_variant
    (fun c => c.pc = some header ∧ I c) guard variant
    (fun c => c.pc = exitLabel ∧ done c) bodyCost exitCost
    (fun c hc hg => exit c hc.1 hc.2 hg)
    (fun c hc hg => by
      obtain ⟨b, hrun, hpc, hI, hdec⟩ := body c hc.1 hc.2 hg
      exact ⟨b, hrun, ⟨hpc, hI⟩, hdec⟩)
    fuel a ⟨ha.1, ha.2.1⟩ ha.2.2

end Block

end BitPrograms

end SubexponentialSAT.ProgramLogic

end OAI.Algorithms
