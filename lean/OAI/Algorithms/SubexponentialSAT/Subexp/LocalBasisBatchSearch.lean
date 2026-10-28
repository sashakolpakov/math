import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchStorage
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchConcreteContext

namespace OAI.Algorithms

/-! Physical staging and execution of one local basis search. -/

namespace SubexponentialSAT.Subexp.LocalBasisBatchProgram

open BitProgram StructuredCalls
open BlockSearchPreparation (restrictState lifted_call)

def matrixRegisters : Fin 18 → Fin 32 := Fin.castAdd 14
def matrixPorts : Fin 65 → Fin 128 := Fin.castAdd 63
def searchRegisters : Fin 24 → Fin 32 := Fin.castAdd 8
def searchPorts (i : Fin 42) : Fin 128 := ⟨65 + i.val, by omega⟩

theorem matrixRegisters_injective : Function.Injective matrixRegisters := Fin.castAdd_injective _ _
theorem matrixPorts_injective : Function.Injective matrixPorts := Fin.castAdd_injective _ _
theorem searchRegisters_injective : Function.Injective searchRegisters := Fin.castAdd_injective _ _
theorem searchPorts_injective : Function.Injective searchPorts := by
  intro a b h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp only [searchPorts] at hval
  omega

def searchInputs : List (Fin 128 × Fin 128) :=
  [(0, 103), (55, 104), (108, 92), (109, 101), (116, 66),
   (124, 73), (123, 74), (123, 86)]

def matrixWork : List (Fin 128) := List.ofFn matrixPorts
def searchWork : List (Fin 128) := List.ofFn searchPorts ++ [124]

def runSearch : Code := .seq (copyMany searchInputs)
  (.seq (clearMany matrixWork)
    (.call (ProgramLinking.liftProgram BlockSearchConcrete.program searchRegisters searchPorts)))

def searchCopied (a : Data) : Data := copyManyState searchInputs a
def searchStaged (a : Data) : Data := clearManyState matrixWork (searchCopied a)

def searchInputStacks (a : Data) (j : Fin 128) : Word :=
  if j = 103 then a.stacks 0 ++ a.stacks j else
  if j = 104 then a.stacks 55 ++ a.stacks j else
  if j = 92 then a.stacks 108 ++ a.stacks j else
  if j = 101 then a.stacks 109 ++ a.stacks j else
  if j = 66 then a.stacks 116 ++ a.stacks j else
  if j = 73 then a.stacks 124 ++ a.stacks j else
  if j = 74 ∨ j = 86 then a.stacks 123 ++ a.stacks j else a.stacks j

theorem searchCopied_stacks (a : Data) : (searchCopied a).stacks = searchInputStacks a := by
  funext j
  by_cases h103 : j = 103
  · subst j; rfl
  by_cases h104 : j = 104
  · subst j; rfl
  by_cases h92 : j = 92
  · subst j; rfl
  by_cases h101 : j = 101
  · subst j; rfl
  by_cases h66 : j = 66
  · subst j; rfl
  by_cases h73 : j = 73
  · subst j; rfl
  by_cases h74 : j = 74
  · subst j; rfl
  by_cases h86 : j = 86
  · subst j; rfl
  simp [searchCopied, searchInputs, copyManyState, copyState, StackRoutines.copyStacks,
    searchInputStacks, h103, h104, h92, h101, h66, h73, h74, h86]

theorem matrixWork_mem (j : Fin 128) : j ∈ matrixWork ↔ j.val < 65 := by
  simp only [matrixWork, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    exact i.isLt
  · intro hj
    exact ⟨⟨j.val, hj⟩, rfl⟩

theorem searchStaged_stacks (a : Data) (j : Fin 128) :
    (searchStaged a).stacks j = if j.val < 65 then [] else searchInputStacks a j := by
  simp only [searchStaged, clearMany_stacks, matrixWork_mem, searchCopied_stacks]

theorem searchStaged_high (a : Data) (j : Fin 128) (hj : 107 ≤ j.val) :
    (searchStaged a).stacks j = a.stacks j := by
  rw [searchStaged_stacks, ite_eq_right (by omega)]
  have hne (k : Fin 128) (hk : k.val < 107) : j ≠ k := by
    intro h
    subst k
    omega
  have h103 := hne 103 (by decide)
  have h104 := hne 104 (by decide)
  have h92 := hne 92 (by decide)
  have h101 := hne 101 (by decide)
  have h66 := hne 66 (by decide)
  have h73 := hne 73 (by decide)
  have h74 := hne 74 (by decide)
  have h86 := hne 86 (by decide)
  simp [searchInputStacks, h103, h104, h92, h101, h66, h73, h74, h86]

theorem copyMany_register_frame (pairs : List (Fin 128 × Fin 128)) (a : Data)
    (j : Fin 32) (h0 : j ≠ 0) (h1 : j ≠ 1) :
    (copyManyState pairs a).regs j = a.regs j := by
  induction pairs generalizing a with
  | nil => rfl
  | cons p ps ih =>
      rw [copyManyState, ih]
      simp [copyState, readRegs, h0, h1]

theorem clearMany_register_frame (ports : List (Fin 128)) (a : Data)
    (j : Fin 32) (h0 : j ≠ 0) (h1 : j ≠ 1) :
    (clearManyState ports a).regs j = a.regs j := by
  induction ports generalizing a with
  | nil => rfl
  | cons k ks ih =>
      rw [clearManyState, ih]
      simp [clearState, readRegs, h0, h1]

theorem searchStaged_register_frame (a : Data) (j : Fin 32) (hj : 2 ≤ j.val) :
    (searchStaged a).regs j = a.regs j := by
  have h0 : j ≠ 0 := by intro h; subst j; exact (by decide : ¬ 2 ≤ (0 : Fin 32).val) hj
  have h1 : j ≠ 1 := by intro h; subst j; exact (by decide : ¬ 2 ≤ (1 : Fin 32).val) hj
  exact (clearMany_register_frame _ _ j h0 h1).trans
    (copyMany_register_frame _ _ j h0 h1)

/-- The values in this predicate are exactly the matrix producer's output
and the retained alphabet/dimension words, before their actual copies. -/
structure SearchReady (p : ℕ) [Fact p.Prime] {m N : ℕ}
    (alphabet : List (ZMod p)) (M : Fin m → Fin N → ZMod p) (a : Data) : Prop where
  matrix : a.stacks 0 = BlockCoefficientProgram.matrixBits p M
  rows : a.stacks 55 = List.replicate m true
  modulus : a.stacks 108 = MatrixWordEncoding.modulus p
  zero : a.stacks 109 = MatrixWordEncoding.zero p
  alphabet : a.stacks 116 = ProgramEncoding.encodeRecords
    (alphabet.map (BlockSearchPredicate.scalarCode p).block)
  dimension : a.stacks 123 = List.replicate N true
  square : a.stacks 124 = List.replicate (N * N) true
  temporary : a.stacks 125 = []
  bank : ∀ i, a.stacks (searchPorts i) = []

def localSearchWords (matrix rows modulus zero alphabet dimension square : Word)
    (i : Fin 42) : Word :=
  if i = 38 then matrix else if i = 39 then rows else
  if i = 27 then modulus else if i = 36 then zero else
  if i = 1 then alphabet else if i = 8 then square else
  if i = 9 ∨ i = 21 then dimension else []

theorem searchStaged_local (a : Data) (empty : ∀ i, a.stacks (searchPorts i) = []) (i : Fin 42) :
    (searchStaged a).stacks (searchPorts i) =
      localSearchWords (a.stacks 0) (a.stacks 55) (a.stacks 108) (a.stacks 109)
        (a.stacks 116) (a.stacks 123) (a.stacks 124) i := by
  rw [searchStaged_stacks, ite_eq_right (by simp [searchPorts])]
  have he := empty i
  have h103 : searchPorts i = 103 ↔ i = 38 :=
    searchPorts_injective.eq_iff' (a := i) (b := 38) rfl
  have h104 : searchPorts i = 104 ↔ i = 39 :=
    searchPorts_injective.eq_iff' (a := i) (b := 39) rfl
  have h92 : searchPorts i = 92 ↔ i = 27 :=
    searchPorts_injective.eq_iff' (a := i) (b := 27) rfl
  have h101 : searchPorts i = 101 ↔ i = 36 :=
    searchPorts_injective.eq_iff' (a := i) (b := 36) rfl
  have h66 : searchPorts i = 66 ↔ i = 1 :=
    searchPorts_injective.eq_iff' (a := i) (b := 1) rfl
  have h73 : searchPorts i = 73 ↔ i = 8 :=
    searchPorts_injective.eq_iff' (a := i) (b := 8) rfl
  have h74 : searchPorts i = 74 ↔ i = 9 :=
    searchPorts_injective.eq_iff' (a := i) (b := 9) rfl
  have h86 : searchPorts i = 86 ↔ i = 21 :=
    searchPorts_injective.eq_iff' (a := i) (b := 21) rfl
  simp only [searchInputStacks, h103, h104, h92, h101, h66, h73, h74, h86,
    he, List.append_nil, localSearchWords]

theorem searchInput_local (p : ℕ) [Fact p.Prime] {m N : ℕ}
    (alphabet : List (ZMod p)) (M : Fin m → Fin N → ZMod p) (regs : Fin 24 → Bool)
    (i : Fin 42) :
    (BlockSearchExecution.inputState (BlockCoefficientProgram.context p M)
      (BlockSearchPredicate.scalarCode p) alphabet N regs).stacks i =
      localSearchWords (BlockCoefficientProgram.matrixBits p M) (List.replicate m true)
        (MatrixWordEncoding.modulus p) (MatrixWordEncoding.zero p)
        (ProgramEncoding.encodeRecords (alphabet.map (BlockSearchPredicate.scalarCode p).block))
        (List.replicate N true) (List.replicate (N * N) true) i := by
  fin_cases i <;> rfl

theorem searchStaged_ready (p : ℕ) [Fact p.Prime] {m N : ℕ}
    (alphabet : List (ZMod p)) (M : Fin m → Fin N → ZMod p) (a : Data)
    (ready : SearchReady p alphabet M a) :
    restrictState searchRegisters searchPorts (searchStaged a) =
      BlockSearchExecution.inputState (BlockCoefficientProgram.context p M)
        (BlockSearchPredicate.scalarCode p) alphabet N
        ((searchStaged a).regs ∘ searchRegisters) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    change (searchStaged a).stacks (searchPorts i) = _
    rw [searchStaged_local a ready.bank, ready.matrix, ready.rows, ready.modulus,
      ready.zero, ready.alphabet, ready.dimension, ready.square]
    exact (searchInput_local p alphabet M _ i).symm

def searchCost (p : ℕ) [Fact p.Prime] (alphabet : List (ZMod p))
    (m N : ℕ) (a : Data) : ℕ :=
  copyManyCost searchInputs a + clearManyCost matrixWork (searchCopied a) +
    BlockSearchExecution.cost (BlockSearchPredicate.scalarCode p) alphabet N
      (BlockCoefficientProgram.coefficientCost p m N)

/-- This executes the physical input copies, clears the old matrix bank,
and invokes the fixed exhaustive search. Only the search bank can retain
enumeration data; the next stage will clear that entire bank. -/
theorem runSearch_eval (p : ℕ) [Fact p.Prime]
    (alphabet : List (ZMod p)) (hfull : ∀ x, x ∈ alphabet) {m N : ℕ}
    (M : Fin m → Fin N → ZMod p) (a : Data) (ready : SearchReady p alphabet M a) :
    ∃ (steps : ℕ) (b : Data) (C : Fin N → Fin N → ZMod p) (d : Fin (N + 1)),
      steps ≤ searchCost p alphabet m N a ∧ Eval runSearch steps a b ∧
      BlockSearch.GoodPair M (BlockSearchEncoding.splitPair d C) ∧
      b.stacks 106 = BlockCoefficientProgram.tableBits p C ∧
      b.stacks 73 = List.replicate d.val true ∧
      b.stacks 75 = List.replicate N true ∧
      (∀ j : Fin 128, j.val < 65 → b.stacks j = []) ∧
      (∀ j : Fin 128, 107 ≤ j.val → b.stacks j = a.stacks j) ∧
      (∀ j : Fin 32, 24 ≤ j.val → b.regs j = a.regs j) := by
  have hc := copyMany_eval searchInputs a (by
    intro pair hp
    simp only [searchInputs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) ready.temporary
  have he := clearMany_eval matrixWork (searchCopied a)
  obtain ⟨next, C, d, hgood, hC, hd, hrun⟩ :=
    BlockSearchConcrete.program_runsIn_with_alphabet p alphabet hfull M
      ((searchStaged a).regs ∘ searchRegisters)
  have hN := BlockSearchConcreteContext.dimension_with_alphabet p alphabet hfull M _ hrun
  have hr := searchStaged_ready p alphabet M a ready
  obtain ⟨ns, hns, hs⟩ := lifted_call BlockSearchConcrete.program searchRegisters searchPorts
    searchRegisters_injective searchPorts_injective (searchStaged a) next _
    (by simpa only [hr] using hrun)
  let b := embedState searchRegisters searchPorts (searchStaged a) next
  have mapped (i : Fin 42) : b.stacks (searchPorts i) = next.stacks i :=
    embedState_stack _ _ _ _ searchPorts_injective i
  have frame (j : Fin 128) (hj : j.val < 65 ∨ 107 ≤ j.val) :
      b.stacks j = (searchStaged a).stacks j := by
    apply embedState_stack_frame
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    simp only [searchPorts] at hv
    omega
  refine ⟨_, b, C, d, ?_, hc.seq (he.seq hs), hgood, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [searchCost]
    omega
  · exact (mapped 41).trans (hC.trans (BlockSearchConcrete.tableBits_eq p C))
  · exact (mapped 8).trans hd
  · exact (mapped 10).trans hN
  · intro j hj
    rw [frame j (Or.inl hj), searchStaged_stacks, ite_eq_left hj]
  · intro j hj
    exact (frame j (Or.inr hj)).trans (searchStaged_high a j hj)
  · intro j hj
    have hf : b.regs j = (searchStaged a).regs j := by
      apply embedState_register_frame
      rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      simp only [searchRegisters, Fin.val_castAdd] at hv
      omega
    exact hf.trans (searchStaged_register_frame a j (by omega))

end SubexponentialSAT.Subexp.LocalBasisBatchProgram

end OAI.Algorithms
