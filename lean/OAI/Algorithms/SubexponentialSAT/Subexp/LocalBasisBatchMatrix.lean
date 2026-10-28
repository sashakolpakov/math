import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintMatrixSemantics

namespace OAI.Algorithms

/-! The batch invokes the actual one-Side matrix producer on copied inputs. -/

namespace SubexponentialSAT.Subexp.LocalBasisBatchProgram

open BitProgram StructuredCalls
open BlockSearchPreparation (restrictState lifted_call)

def matrixCopied (a : Data) : Data := copyManyState matrixInputs a

def matrixInputStacks (a : Data) (j : Fin 128) : Word :=
  if j = 21 then a.stacks 112 ++ a.stacks j else
  if j = 22 then a.stacks 113 ++ a.stacks j else
  if j = 26 then a.stacks 114 ++ a.stacks j else
  if j = 29 then a.stacks 108 ++ a.stacks j else
  if j = 30 then a.stacks 109 ++ a.stacks j else
  if j = 31 then a.stacks 110 ++ a.stacks j else
  if j = 32 then a.stacks 111 ++ a.stacks j else
  if j = 37 then a.stacks 117 ++ a.stacks j else
  if j = 62 then a.stacks 118 ++ a.stacks j else
  if j = 64 then a.stacks 115 ++ a.stacks j else a.stacks j

theorem matrixCopied_stacks (a : Data) : (matrixCopied a).stacks = matrixInputStacks a := by
  funext j
  by_cases h21 : j = 21
  · subst j; rfl
  by_cases h22 : j = 22
  · subst j; rfl
  by_cases h26 : j = 26
  · subst j; rfl
  by_cases h29 : j = 29
  · subst j; rfl
  by_cases h30 : j = 30
  · subst j; rfl
  by_cases h31 : j = 31
  · subst j; rfl
  by_cases h32 : j = 32
  · subst j; rfl
  by_cases h37 : j = 37
  · subst j; rfl
  by_cases h62 : j = 62
  · subst j; rfl
  by_cases h64 : j = 64
  · subst j; rfl
  simp [matrixCopied, matrixInputs, copyManyState, copyState, StackRoutines.copyStacks,
    matrixInputStacks, h21, h22, h26, h29, h30, h31, h32, h37, h62, h64]

theorem matrixCopied_high (a : Data) (j : Fin 128) (hj : 65 ≤ j.val) :
    (matrixCopied a).stacks j = a.stacks j := by
  apply copyMany_frame
  intro pair hp he
  have ht : pair.2.val < 65 := by
    simp only [matrixInputs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hv := congrArg Fin.val he
  omega

structure MatrixReady (p : ℕ) [Fact p.Prime] (r Q Δ t g : ℕ)
    (coefficients : List (ZMod p)) (side : List Word) (a : Data) : Prop where
  colors : a.stacks 112 = List.replicate r true
  positions : a.stacks 113 = List.replicate Q true
  width : a.stacks 114 = List.replicate (Q * r) true
  slots : a.stacks 115 = List.replicate Δ true
  position : a.stacks 117 = List.replicate t true
  color : a.stacks 118 = List.replicate g true
  modulus : a.stacks 108 = MatrixWordEncoding.modulus p
  zero : a.stacks 109 = MatrixWordEncoding.word p 0
  coefficientsWord : a.stacks 110 = CoefficientPascalProgram.valueWords p coefficients
  count : a.stacks 111 = List.replicate coefficients.length true
  side : a.stacks 53 = ProgramEncoding.encodeRecords side
  work : ∀ j : Fin 128, j.val < 65 → j ≠ 53 → a.stacks j = []
  temporary : a.stacks 125 = []

theorem matrixCopied_ready (p : ℕ) [Fact p.Prime] (r Q Δ t g : ℕ)
    (coefficients : List (ZMod p)) (side : List Word) (a : Data)
    (ready : MatrixReady p r Q Δ t g coefficients side a) :
    restrictState matrixRegisters matrixPorts (matrixCopied a) =
      ConstraintMatrixProgram.input p r Q Δ t g coefficients side
        ((matrixCopied a).regs ∘ matrixRegisters) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    change (matrixCopied a).stacks (matrixPorts i) = _
    rw [matrixCopied_stacks]
    by_cases hi : i = 53
    · subst i
      simpa [matrixInputStacks, matrixPorts, ConstraintMatrixProgram.input] using ready.side
    · have hwork : a.stacks (matrixPorts i) = [] := ready.work _ i.isLt (by
        intro h
        exact hi (matrixPorts_injective h))
      have h21 : matrixPorts i = 21 ↔ i = 21 := matrixPorts_injective.eq_iff' (a := i) (b := 21) rfl
      have h22 : matrixPorts i = 22 ↔ i = 22 := matrixPorts_injective.eq_iff' (a := i) (b := 22) rfl
      have h26 : matrixPorts i = 26 ↔ i = 26 := matrixPorts_injective.eq_iff' (a := i) (b := 26) rfl
      have h29 : matrixPorts i = 29 ↔ i = 29 := matrixPorts_injective.eq_iff' (a := i) (b := 29) rfl
      have h30 : matrixPorts i = 30 ↔ i = 30 := matrixPorts_injective.eq_iff' (a := i) (b := 30) rfl
      have h31 : matrixPorts i = 31 ↔ i = 31 := matrixPorts_injective.eq_iff' (a := i) (b := 31) rfl
      have h32 : matrixPorts i = 32 ↔ i = 32 := matrixPorts_injective.eq_iff' (a := i) (b := 32) rfl
      have h37 : matrixPorts i = 37 ↔ i = 37 := matrixPorts_injective.eq_iff' (a := i) (b := 37) rfl
      have h62 : matrixPorts i = 62 ↔ i = 62 := matrixPorts_injective.eq_iff' (a := i) (b := 62) rfl
      have h64 : matrixPorts i = 64 ↔ i = 64 := matrixPorts_injective.eq_iff' (a := i) (b := 64) rfl
      simp only [matrixInputStacks, h21, h22, h26, h29, h30, h31, h32, h37, h62, h64,
        hwork, List.append_nil, hi, ite_false,
        ready.colors, ready.positions, ready.width, ready.slots, ready.position, ready.color,
        ready.modulus, ready.zero, ready.coefficientsWord, ready.count]

noncomputable def buildMatrixCost (p : ℕ) [Fact p.Prime] {r Q Δ : ℕ}
    (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r)
    (coefficients : List (ZMod p)) (E : ℕ) (a : Data) : ℕ :=
  copyManyCost matrixInputs a +
    ConstraintMatrixProgram.budget (Δ := Δ) p hr hQ t g coefficients E

theorem buildMatrix_eval (p : ℕ) [Fact p.Prime] {r Q Δ : ℕ}
    (h2 : (2 : ZMod p) ≠ 0) (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r)
    (coefficients : List (ZMod p)) (E : ℕ)
    (hE : ∀ i : Fin Δ, ∀ u ∈ ConstraintMatrixProgram.rows hr hQ t g i,
      ∀ y ∈ ConstraintMatrixProgram.columns hr hQ t g,
        ConstraintEntryProgram.programBudget p i t u y coefficients ≤ E)
    (a : Data) (ready : MatrixReady p r Q Δ t.val g.val coefficients
      (TypeEnumeration.sideBytes r Q Δ t.val g.val) a) :
    ∃ steps b, steps ≤ buildMatrixCost (Δ := Δ) p hr hQ t g coefficients E a ∧
      Eval buildMatrix steps a b ∧
      b.stacks 0 = BlockCoefficientProgram.matrixBits p
        (ConstraintMatrixProgram.matrix (Δ := Δ) p hr hQ t g coefficients) ∧
      b.stacks 55 = List.replicate (ConstraintMatrixProgram.rowList (Δ := Δ) hr hQ t g).length true ∧
      (∀ j : Fin 128, 65 ≤ j.val → b.stacks j = a.stacks j) ∧
      (∀ j : Fin 32, 18 ≤ j.val → b.regs j = a.regs j) := by
  have hc := copyMany_eval matrixInputs a (by
    intro pair hp
    simp only [matrixInputs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    ready.temporary
  have hrdy := matrixCopied_ready p r Q Δ t.val g.val coefficients _ a ready
  obtain ⟨out, hrun⟩ := ConstraintMatrixProgram.program_runsIn p h2 hr hQ t g coefficients
    E hE ((matrixCopied a).regs ∘ matrixRegisters)
  obtain ⟨nm, hnm, hm⟩ := lifted_call ConstraintMatrixProgram.program matrixRegisters matrixPorts
    matrixRegisters_injective matrixPorts_injective (matrixCopied a)
    (ConstraintMatrixProgram.output (Δ := Δ) p hr hQ t g coefficients out) _
    (by simpa only [hrdy] using hrun)
  let b := embedState matrixRegisters matrixPorts (matrixCopied a)
    (ConstraintMatrixProgram.output (Δ := Δ) p hr hQ t g coefficients out)
  have mapped (j : Fin 65) : b.stacks (matrixPorts j) =
      (ConstraintMatrixProgram.output (Δ := Δ) p hr hQ t g coefficients out).stacks j :=
    embedState_stack _ _ _ _ matrixPorts_injective j
  refine ⟨_, b, Nat.add_le_add_left hnm _, hc.seq hm, ?_, ?_, ?_, ?_⟩
  · exact (mapped 0).trans (ConstraintMatrixProgram.output_matrix p hr hQ t g coefficients out)
  · exact (mapped 55).trans (ConstraintMatrixProgram.output_rows p hr hQ t g coefficients out)
  · intro j hj
    have hf : b.stacks j = (matrixCopied a).stacks j := by
      apply embedState_stack_frame
      rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      simp only [matrixPorts, Fin.val_castAdd] at hv
      omega
    exact hf.trans (matrixCopied_high a j hj)
  · intro j hj
    have hf : b.regs j = (matrixCopied a).regs j := by
      apply embedState_register_frame
      rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      simp only [matrixRegisters, Fin.val_castAdd] at hv
      omega
    exact hf.trans (copyMany_register_frame _ _ j
      (by intro h; subst j; exact (by decide : ¬18 ≤ (0 : Fin 32).val) hj)
      (by intro h; subst j; exact (by decide : ¬18 ≤ (1 : Fin 32).val) hj))

end SubexponentialSAT.Subexp.LocalBasisBatchProgram

end OAI.Algorithms
