import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramMass
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramBranches

namespace OAI.Algorithms

/-! The branch callback is a real residual-count program followed by the native
binary adder. Semantic branch counts occur only in its verification contract. -/
namespace SubexponentialSAT.SqrtLog.LeafBranchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.ExecCNFTupleEnumeration

structure Ports (R S : ℕ) where
  counter : CounterForPrograms.Ports R S
  mass : SqrtLog.LeafProgram.Mass.Ports R S
  disjoint_counter : ∀ i, mass.stack i ≠ counter.counter
  disjoint_scratch : ∀ i, mass.stack i ≠ counter.scratch

variable {R S : ℕ}

def read (p : Ports R S) (a : State R S) := a.stacks (p.mass.stack 0)
def Ready (p : Ports R S) (I : State R S → Prop) (a : State R S) :=
  I a ∧ a.stacks (p.mass.stack 1) = [] ∧ a.stacks (p.mass.stack 2) = []
def MassStable (p : Ports R S) (I : State R S → Prop) : Prop :=
  ∀ a regs acc next, I a → I (LeafProgram.Mass.state p.mass a regs acc next)

theorem mass_self (p : Ports R S) (a : State R S)
    (hs : a.stacks (p.mass.stack 2) = []) :
    LeafProgram.Mass.state p.mass a (fun i => a.regs (p.mass.register i))
      (read p a) (a.stacks (p.mass.stack 1)) = a := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases h : ∃ j, p.mass.register j = i
    · obtain ⟨j, rfl⟩ := h
      exact embedState_register p.mass.register p.mass.stack a
        (LeafProgram.Mass.data (fun i => a.regs (p.mass.register i))
          (read p a) (a.stacks (p.mass.stack 1))) p.mass.register_injective j
    · exact embedState_register_frame p.mass.register p.mass.stack a
        (LeafProgram.Mass.data (fun i => a.regs (p.mass.register i))
          (read p a) (a.stacks (p.mass.stack 1))) i h
  · funext i
    by_cases h : ∃ j, p.mass.stack j = i
    · obtain ⟨j, rfl⟩ := h
      calc
        _ = (LeafProgram.Mass.data (fun i => a.regs (p.mass.register i))
          (read p a) (a.stacks (p.mass.stack 1))).stacks j :=
            embedState_stack p.mass.register p.mass.stack a _ p.mass.stack_injective j
        _ = _ := by
          fin_cases j <;> simp [LeafProgram.Mass.data, BinaryPrograms.Add.stackState, read, hs]
    · exact embedState_stack_frame p.mass.register p.mass.stack a
        (LeafProgram.Mass.data (fun i => a.regs (p.mass.register i))
          (read p a) (a.stacks (p.mass.stack 1))) i h

theorem mass_stack (p : Ports R S) (a : State R S) regs acc next (i : Fin 3) :
    (LeafProgram.Mass.state p.mass a regs acc next).stacks (p.mass.stack i) =
      (LeafProgram.Mass.data regs acc next).stacks i :=
  embedState_stack _ _ _ _ p.mass.stack_injective i

theorem mass_frame (p : Ports R S) (a : State R S) regs acc next (j : Fin S)
    (hj : ∀ i, p.mass.stack i ≠ j) :
    (LeafProgram.Mass.state p.mass a regs acc next).stacks j = a.stacks j := by
  apply embedState_stack_frame
  rintro ⟨i, hi⟩
  exact hj i hi

/-- A residual count must actually run and emit a bounded binary word. -/
abbrev ResidualSpec (p : Ports R S) (query : Cmd R S) (shape : List ℕ)
    (I : State R S → Prop) (budget width : ℕ) (value : ℕ → ℕ) : Prop :=
  ∀ words a, words.map List.length = shape → Ready p I a →
    a.stacks p.counter.counter = Encoding.encodeList id words →
    a.stacks p.counter.scratch = [] →
    ∃ n b, n ≤ budget ∧ Eval query n a b ∧ I b ∧
      b.stacks p.counter.counter = Encoding.encodeList id words ∧
      b.stacks p.counter.scratch = [] ∧ read p b = read p a ∧
      b.stacks (p.mass.stack 2) = [] ∧
      (b.stacks (p.mass.stack 1)).length ≤ width ∧
      BinaryArithmetic.toNat (b.stacks (p.mass.stack 1)) = value (CounterPrograms.value words.flatten)

abbrev body (p : Ports R S) (query : Cmd R S) :=
  Cmd.seq query (LeafProgram.Mass.invoke p.mass)

/-- The native callback both adds the computed count and empties its input. -/
theorem body_step (p : Ports R S) (query : Cmd R S) (shape : List ℕ)
    (I : State R S → Prop) (budget width : ℕ) (value : ℕ → ℕ)
    (stable : MassStable p I) (spec : ResidualSpec p query shape I budget width value)
    (words : List (List Bool)) (a : State R S) (hw : words.map List.length = shape)
    (hi : Ready p I a) (hc : a.stacks p.counter.counter = Encoding.encodeList id words)
    (hs : a.stacks p.counter.scratch = []) :
    ∃ n b, n ≤ budget + 16 * ((read p a).length + width + 1) + 3 ∧
      Eval (body p query) n a b ∧ Ready p I b ∧
      b.stacks p.counter.counter = Encoding.encodeList id words ∧
      b.stacks p.counter.scratch = [] ∧
      (read p b).length ≤ (read p a).length + width + 1 ∧
      BinaryArithmetic.toNat (read p b) = BinaryArithmetic.toNat (read p a) +
        value (CounterPrograms.value words.flatten) := by
  obtain ⟨n, b, hn, he, hbi, hbc, hbs, hacc, htmp, hwidth, hvalue⟩ :=
    spec words a hw hi hc hs
  obtain ⟨m, hm, regs, ha⟩ := LeafProgram.Mass.invoke_eval p.mass b
    (fun i => b.regs (p.mass.register i)) (read p b) (b.stacks (p.mass.stack 1))
  rw [mass_self p b htmp] at ha
  let out := BinaryArithmetic.add (read p b) (b.stacks (p.mass.stack 1))
  let c := LeafProgram.Mass.state p.mass b regs out []
  have hread : read p c = out := mass_stack p b regs out [] 0
  have hone : c.stacks (p.mass.stack 1) = [] := mass_stack p b regs out [] 1
  have htwo : c.stacks (p.mass.stack 2) = [] := mass_stack p b regs out [] 2
  have hlen := BinaryArithmetic.length_add (read p b) (b.stacks (p.mass.stack 1))
  have hmax : max (read p b).length (b.stacks (p.mass.stack 1)).length ≤
      (read p a).length + width := by rw [hacc]; omega
  refine ⟨n+m, c, by omega, he.seq ha, ⟨stable b regs out [] hbi, hone, htwo⟩,
    ?_, ?_, ?_, ?_⟩
  · exact (mass_frame p b regs out [] _ p.disjoint_counter).trans hbc
  · exact (mass_frame p b regs out [] _ p.disjoint_scratch).trans hbs
  · rw [hread]; exact hlen.trans (by omega)
  · rw [hread, BinaryArithmetic.toNat_add, hacc, hvalue]

/-- Concrete shared ports used inside the marked-clause collector. -/
def fixedPorts : Ports 22 340 where
  counter := {
    register := ⟨fun i => ⟨19 + i.val, by omega⟩, by intro i j h; apply Fin.ext; simpa using congrArg Fin.val h⟩
    counter := 330
    scratch := 331
    counter_ne_scratch := by decide }
  mass := {
    register := fun i => i.castAdd 14
    stack := ![332,323,324]
    register_injective := Fin.castAdd_injective 8 14
    stack_injective := by decide }
  disjoint_counter := by decide
  disjoint_scratch := by decide

end SubexponentialSAT.SqrtLog.LeafBranchProgram

end OAI.Algorithms
