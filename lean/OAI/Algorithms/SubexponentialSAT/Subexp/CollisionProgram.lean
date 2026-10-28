import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalExpectation
import OAI.Algorithms.SubexponentialSAT.ExecClauseCost
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-!
# A fixed bit-program implementation of type collision

Each color is represented by an r-bit one-hot word.  All head and slot words
are serialized at a fixed width.  The existing fixed bitEqualityProgram
then compares two such encodings, including at the primitive-machine level.
The execution boundary has the two encoded types already on its two stacks;
seed lookup and the production of these encodings are separate operations.
-/

namespace SubexponentialSAT.Subexp.CollisionProgram

open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.BitProgram

variable {r Q Δ : ℕ}

/-- The exact length of every type encoding. -/
def typeWidth (r Q Δ : ℕ) : ℕ := ((Δ + 1) * Q) * r

/-- Register zero is the head, and register i+1 is slot i. -/
def registerWord (u : UniversalType r Q Δ) (a : Fin (Δ + 1)) : Word r Q :=
  Fin.cases u.head u.slot a

@[simp] theorem registerWord_zero (u : UniversalType r Q Δ) :
    registerWord u 0 = u.head := rfl

@[simp] theorem registerWord_succ (u : UniversalType r Q Δ) (i : Fin Δ) :
    registerWord u i.succ = u.slot i := by
  simp [registerWord]

/-- A computable position in the flattened register-position-color order. -/
def codeIndex (a : Fin (Δ + 1)) (q : Fin Q) (c : Fin r) : Fin (typeWidth r Q Δ) :=
  finProdFinEquiv (finProdFinEquiv (a, q), c)

/-- One bit of the one-hot representation. -/
def codeBit (u : UniversalType r Q Δ) (j : Fin (typeWidth r Q Δ)) : Bool :=
  let outer : Fin ((Δ + 1) * Q) × Fin r := finProdFinEquiv.symm j
  let inner : Fin (Δ + 1) × Fin Q := finProdFinEquiv.symm outer.1
  decide (registerWord u inner.1 inner.2 = outer.2)

@[simp] theorem codeBit_codeIndex (u : UniversalType r Q Δ)
    (a : Fin (Δ + 1)) (q : Fin Q) (c : Fin r) :
    codeBit u (codeIndex a q c) = decide (registerWord u a q = c) := by
  simp [codeBit, codeIndex]

/-- Uniform, fixed-width serialization of all type registers. -/
def encodeType (u : UniversalType r Q Δ) : List Bool := List.ofFn (codeBit u)

@[simp] theorem encodeType_length (u : UniversalType r Q Δ) :
    (encodeType u).length = typeWidth r Q Δ := by
  simp [encodeType]

theorem encodeType_injective :
    Function.Injective (encodeType : UniversalType r Q Δ → List Bool) := by
  intro u v h
  have hbits : codeBit u = codeBit v := List.ofFn_injective h
  have hreg : registerWord u = registerWord v := by
    funext a q
    have hb := congrFun hbits (codeIndex a q (registerWord u a q))
    simp only [codeBit_codeIndex, decide_true] at hb
    exact (of_decide_eq_true hb.symm).symm
  apply UniversalType.ext
  · exact congrFun hreg 0
  · funext i
    exact congrFun hreg i.succ

@[simp] theorem encodeType_eq_iff (u v : UniversalType r Q Δ) :
    encodeType u = encodeType v ↔ u = v :=
  encodeType_injective.eq_iff

/-- The collision output specification.  Its implementation is the fixed
bitEqualityProgram, not evaluation of this proposition by a machine oracle. -/
def collisionBool (u v : UniversalType r Q Δ) : Bool := decide (u = v)

/-- Exact source-instruction upper bound, including the final empty-stack test. -/
def collisionBudget (r Q Δ : ℕ) : ℕ := 9 * (typeWidth r Q Δ + 1)

def collisionStart (regs : Fin 5 → Bool) (u v : UniversalType r Q Δ) : Cfg 5 2 10 :=
  SubexponentialSAT.ExecClauseCost.bitEqualityStart regs (encodeType u) (encodeType v)

/-- The existing ten-label program executes a correct type comparison.
All growing parameters appear only in the stack data. -/
theorem collision_trace (regs : Fin 5 → Bool) (u v : UniversalType r Q Δ) :
    ∃ n ≤ collisionBudget r Q Δ, ∃ c : Cfg 5 2 10,
      Trace SubexponentialSAT.ExecClauseCost.bitEqualityProgram n (collisionStart regs u v) c ∧
      c.pc = none ∧ c.regs 4 = collisionBool u v := by
  obtain ⟨n, hn, c, ht, hp, hout⟩ :=
    SubexponentialSAT.ExecClauseCost.bitEquality_runs regs (encodeType u) (encodeType v)
  refine ⟨n, ?_, c, ht, hp, ?_⟩
  · simpa [collisionBudget] using hn
  · simpa [collisionBool] using hout

theorem collision_runsIn (regs : Fin 5 → Bool) (u v : UniversalType r Q Δ) :
    ∃ c : Cfg 5 2 10,
      RunsIn SubexponentialSAT.ExecClauseCost.bitEqualityProgram (collisionBudget r Q Δ)
        (collisionStart regs u v) c ∧
      c.pc = none ∧ c.regs 4 = collisionBool u v ∧
      (c.stacks 0).length ≤ typeWidth r Q Δ ∧
      (c.stacks 1).length ≤ typeWidth r Q Δ := by
  obtain ⟨c, ht, hp, hout, h0, h1⟩ :=
    SubexponentialSAT.ExecClauseCost.bitEquality_runsIn_bounded regs (encodeType u) (encodeType v)
  refine ⟨c, ?_, hp, ?_, ?_, ?_⟩
  · simpa [collisionBudget, collisionStart] using ht
  · simpa [collisionBool] using hout
  · simpa using h0
  · simpa using h1

/-- Primitive overhead is a constant of the one fixed equality program. -/
noncomputable def primitiveCollisionBudget (r Q Δ : ℕ) : ℕ :=
  primitiveOverhead SubexponentialSAT.ExecClauseCost.bitEqualityProgram * collisionBudget r Q Δ

theorem collision_primitive_runs (regs : Fin 5 → Bool) (u v : UniversalType r Q Δ) :
    ∃ c : Cfg 5 2 10,
      SubexponentialSAT.Computation.RunsIn
        (primitive SubexponentialSAT.ExecClauseCost.bitEqualityProgram).step
        (primitiveCollisionBudget r Q Δ)
        (primitiveCfg SubexponentialSAT.ExecClauseCost.bitEqualityProgram (collisionStart regs u v))
        (primitiveCfg SubexponentialSAT.ExecClauseCost.bitEqualityProgram c) ∧
      c.pc = none ∧ c.regs 4 = collisionBool u v ∧
      (c.stacks 0).length ≤ typeWidth r Q Δ ∧
      (c.stacks 1).length ≤ typeWidth r Q Δ := by
  obtain ⟨c, ht, hp, hout, h0, h1⟩ :=
    SubexponentialSAT.ExecClauseCost.bitEquality_primitive_runs regs (encodeType u) (encodeType v)
  refine ⟨c, ?_, hp, ?_, ?_, ?_⟩
  · simpa [primitiveCollisionBudget, collisionBudget, collisionStart] using ht
  · simpa [collisionBool] using hout
  · simpa using h0
  · simpa using h1

theorem collisionBudget_linear (hr : 0 < r) (hQ : 0 < Q) :
    collisionBudget r Q Δ ≤ 18 * ((Δ + 1) * Q * r) := by
  have hw : 0 < typeWidth r Q Δ := by
    exact Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) hQ) hr
  dsimp [collisionBudget, typeWidth] at *
  omega

theorem primitiveCollisionBudget_linear (hr : 0 < r) (hQ : 0 < Q) :
    primitiveCollisionBudget r Q Δ ≤
      (18 * primitiveOverhead SubexponentialSAT.ExecClauseCost.bitEqualityProgram) *
        ((Δ + 1) * Q * r) := by
  have h := Nat.mul_le_mul_left (primitiveOverhead SubexponentialSAT.ExecClauseCost.bitEqualityProgram)
    (collisionBudget_linear (Δ := Δ) hr hQ)
  rw [primitiveCollisionBudget]
  calc
    _ ≤ primitiveOverhead SubexponentialSAT.ExecClauseCost.bitEqualityProgram *
        (18 * ((Δ + 1) * Q * r)) := h
    _ = (18 * primitiveOverhead SubexponentialSAT.ExecClauseCost.bitEqualityProgram) *
        ((Δ + 1) * Q * r) := by ring

/-- Reuse the existing equality subroutine, then expose register 4 on the
output stack before the final halt.  No equality instructions are duplicated. -/
def outputCommand : SubexponentialSAT.StructuredCalls.Cmd 5 2 :=
  .seq (.call SubexponentialSAT.ExecClauseCost.bitEqualityProgram)
    (.base (.atom (.push 0 4)))

abbrev outputProgram : Program 5 2 12 :=
  SubexponentialSAT.StructuredCalls.compiled outputCommand 0 0

def outputStart (regs : Fin 5 → Bool) (u v : UniversalType r Q Δ) : Cfg 5 2 12 :=
  ⟨some outputProgram.entry, regs,
    SubexponentialSAT.ExecClauseCost.bitStacks (encodeType u) (encodeType v)⟩

/-- The linked output routine needs just one push and one final halt beyond
the equality subroutine's already-counted return instruction. -/
theorem collisionOutput_trace (regs : Fin 5 → Bool) (u v : UniversalType r Q Δ) :
    ∃ n ≤ collisionBudget r Q Δ + 2, ∃ c : Cfg 5 2 12,
      Trace outputProgram n (outputStart regs u v) c ∧ c.pc = none ∧
      (c.stacks 0).head? = some (collisionBool u v) := by
  obtain ⟨n, hn, c, ht, hp, hout⟩ := collision_trace regs u v
  let a : SubexponentialSAT.StructuredProgram.State 5 2 :=
    ⟨regs, SubexponentialSAT.ExecClauseCost.bitStacks (encodeType u) (encodeType v)⟩
  let b : SubexponentialSAT.StructuredProgram.State 5 2 := ⟨c.regs, c.stacks⟩
  have hcfg : b.withPC none = c := by
    cases c
    simp_all [b, SubexponentialSAT.StructuredProgram.State.withPC]
  have ht' : Trace SubexponentialSAT.ExecClauseCost.bitEqualityProgram n
      (a.withPC (some SubexponentialSAT.ExecClauseCost.bitEqualityProgram.entry))
      (b.withPC none) := by
    rw [hcfg]
    exact ht
  let d := (SubexponentialSAT.StructuredProgram.Atom.push (0 : Fin 2) (4 : Fin 5)).eval b
  have he : SubexponentialSAT.StructuredCalls.Eval outputCommand (n + 1) a d :=
    .seq (.call _ ht') (.base (.atom _ _))
  have hr := SubexponentialSAT.StructuredCalls.compiled_halt_trace he (0 : Fin 2) 0
  refine ⟨n + 1 + 1, by omega, d.withPC none, hr, rfl, ?_⟩
  simp [d, b, SubexponentialSAT.StructuredProgram.Atom.eval,
    SubexponentialSAT.StructuredProgram.Atom.instr, SubexponentialSAT.StructuredProgram.State.ofCfg, execInstr, hout]

noncomputable def primitiveOutputBudget (r Q Δ : ℕ) : ℕ :=
  primitiveOverhead outputProgram * (collisionBudget r Q Δ + 2)

/-- A real primitive-machine run whose terminal answer is the collision bit,
not merely an auxiliary register fact at a source boundary. -/
theorem collisionOutput_primitive_runs (regs : Fin 5 → Bool)
    (u v : UniversalType r Q Δ) :
    ∃ c : (primitive outputProgram).Cfg,
      SubexponentialSAT.Computation.RunsIn (primitive outputProgram).step
        (primitiveOutputBudget r Q Δ)
        (primitiveCfg outputProgram (outputStart regs u v)) c ∧
      c.state = .inl (collisionBool u v) := by
  obtain ⟨n, hn, c, ht, hp, hout⟩ := collisionOutput_trace regs u v
  refine ⟨primitiveCfg outputProgram c, primitive_execution outputProgram ⟨n, hn, ht⟩, ?_⟩
  rw [primitive_halted outputProgram c hp]
  change Sum.inl ((c.stacks 0).head?.getD false) = Sum.inl (collisionBool u v)
  rw [hout]
  rfl

theorem collisionOutputBudget_linear (hr : 0 < r) (hQ : 0 < Q) :
    collisionBudget r Q Δ + 2 ≤ 20 * ((Δ + 1) * Q * r) := by
  have hw : 0 < typeWidth r Q Δ :=
    Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) hQ) hr
  dsimp [collisionBudget, typeWidth] at *
  omega

theorem primitiveOutputBudget_linear (hr : 0 < r) (hQ : 0 < Q) :
    primitiveOutputBudget r Q Δ ≤
      (20 * primitiveOverhead outputProgram) * ((Δ + 1) * Q * r) := by
  have h := Nat.mul_le_mul_left (primitiveOverhead outputProgram)
    (collisionOutputBudget_linear (Δ := Δ) hr hQ)
  simpa [primitiveOutputBudget, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

section AssignedTypes

open SubexponentialSAT.SubexpTypeVariance SubexponentialSAT.SlotAssignment

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]
variable (P : SubexponentialSAT.Factor.Pattern V E) (slots : SlotMap P Δ)

def assignedCollisionStart (regs : Fin 5 → Bool)
    (pair : V × V) (ω : Assignment V E r Q Δ) : Cfg 5 2 10 :=
  collisionStart regs (assignmentType P slots ω pair.1) (assignmentType P slots ω pair.2)

omit [DecidableEq E] in
theorem assignedCollision_trace (regs : Fin 5 → Bool)
    (pair : V × V) (ω : Assignment V E r Q Δ) :
    ∃ n ≤ collisionBudget r Q Δ, ∃ c : Cfg 5 2 10,
      Trace SubexponentialSAT.ExecClauseCost.bitEqualityProgram n (assignedCollisionStart P slots regs pair ω) c ∧
      c.pc = none ∧ c.regs 4 =
        collisionBool (assignmentType P slots ω pair.1) (assignmentType P slots ω pair.2) ∧
      (c.regs 4).toNat = SubexponentialSAT.Subexp.LocalExpectation.naturalPairTerm P slots pair ω := by
  obtain ⟨n, hn, c, ht, hp, hout⟩ := collision_trace regs
    (assignmentType P slots ω pair.1) (assignmentType P slots ω pair.2)
  refine ⟨n, hn, c, ht, hp, hout, ?_⟩
  rw [hout]
  by_cases he : assignmentType P slots ω pair.1 = assignmentType P slots ω pair.2 <;>
    simp [collisionBool, SubexponentialSAT.Subexp.LocalExpectation.naturalPairTerm, he]

omit [DecidableEq E] in
theorem assignedCollision_primitive_runs (regs : Fin 5 → Bool)
    (pair : V × V) (ω : Assignment V E r Q Δ) :
    ∃ c : Cfg 5 2 10,
      SubexponentialSAT.Computation.RunsIn
        (primitive SubexponentialSAT.ExecClauseCost.bitEqualityProgram).step
        (primitiveCollisionBudget r Q Δ)
        (primitiveCfg SubexponentialSAT.ExecClauseCost.bitEqualityProgram
          (assignedCollisionStart P slots regs pair ω))
        (primitiveCfg SubexponentialSAT.ExecClauseCost.bitEqualityProgram c) ∧
      c.pc = none ∧
      (c.regs 4).toNat = SubexponentialSAT.Subexp.LocalExpectation.naturalPairTerm P slots pair ω ∧
      (c.stacks 0).length ≤ typeWidth r Q Δ ∧
      (c.stacks 1).length ≤ typeWidth r Q Δ := by
  obtain ⟨c, ht, hp, hout, h0, h1⟩ := collision_primitive_runs regs
    (assignmentType P slots ω pair.1) (assignmentType P slots ω pair.2)
  refine ⟨c, ht, hp, ?_, h0, h1⟩
  rw [hout]
  by_cases he : assignmentType P slots ω pair.1 = assignmentType P slots ω pair.2 <;>
    simp [collisionBool, SubexponentialSAT.Subexp.LocalExpectation.naturalPairTerm, he]

omit [DecidableEq E] in
/-- The linked routine exposes the actual naturalPairTerm as its terminal bit. -/
theorem assignedCollisionOutput_primitive_runs (regs : Fin 5 → Bool)
    (pair : V × V) (ω : Assignment V E r Q Δ) :
    ∃ c : (primitive outputProgram).Cfg,
      SubexponentialSAT.Computation.RunsIn (primitive outputProgram).step
        (primitiveOutputBudget r Q Δ)
        (primitiveCfg outputProgram
          (outputStart regs (assignmentType P slots ω pair.1) (assignmentType P slots ω pair.2))) c ∧
      c.state = .inl (decide (SubexponentialSAT.Subexp.LocalExpectation.naturalPairTerm P slots pair ω = 1)) := by
  obtain ⟨c, ht, hout⟩ := collisionOutput_primitive_runs regs
    (assignmentType P slots ω pair.1) (assignmentType P slots ω pair.2)
  refine ⟨c, ht, ?_⟩
  rw [hout]
  by_cases he : assignmentType P slots ω pair.1 = assignmentType P slots ω pair.2 <;>
    simp [collisionBool, SubexponentialSAT.Subexp.LocalExpectation.naturalPairTerm, he]

end AssignedTypes

end SubexponentialSAT.Subexp.CollisionProgram

end OAI.Algorithms
