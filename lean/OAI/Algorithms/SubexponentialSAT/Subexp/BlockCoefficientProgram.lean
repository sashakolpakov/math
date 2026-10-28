import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEncodedProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixWordEncoding
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchLoop
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCoefficientContext
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCoefficientAssembly
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixZeroSemantics
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchPredicate
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchTailSemantics

namespace OAI.Algorithms

/-!
# The local arithmetic call inside the encoded basis search

The two-product table is relocated into work stacks 22--41. Its finite
instructions use only registers 0--7; both surrounding iterator controllers
are framed by construction.
-/

namespace SubexponentialSAT.Subexp.BlockCoefficientProgram

open BitProgram StructuredCalls

-- Explicit closed-port projections also discharge the dependent conditions in
-- the installed 20-stack state and the surrounding 42-stack work area.
@[local simp] private theorem localPort0_val : ((0 : Fin 20) : ℕ) = 0 := rfl
@[local simp] private theorem localPort1_val : ((1 : Fin 20) : ℕ) = 1 := rfl
@[local simp] private theorem localPort2_val : ((2 : Fin 20) : ℕ) = 2 := rfl
@[local simp] private theorem localPort3_val : ((3 : Fin 20) : ℕ) = 3 := rfl
@[local simp] private theorem localPort4_val : ((4 : Fin 20) : ℕ) = 4 := rfl
@[local simp] private theorem localPort5_val : ((5 : Fin 20) : ℕ) = 5 := rfl
@[local simp] private theorem localPort6_val : ((6 : Fin 20) : ℕ) = 6 := rfl
@[local simp] private theorem localPort7_val : ((7 : Fin 20) : ℕ) = 7 := rfl
@[local simp] private theorem localPort8_val : ((8 : Fin 20) : ℕ) = 8 := rfl
@[local simp] private theorem localPort9_val : ((9 : Fin 20) : ℕ) = 9 := rfl
@[local simp] private theorem localPort10_val : ((10 : Fin 20) : ℕ) = 10 := rfl
@[local simp] private theorem localPort11_val : ((11 : Fin 20) : ℕ) = 11 := rfl
@[local simp] private theorem localPort12_val : ((12 : Fin 20) : ℕ) = 12 := rfl
@[local simp] private theorem localPort13_val : ((13 : Fin 20) : ℕ) = 13 := rfl
@[local simp] private theorem localPort14_val : ((14 : Fin 20) : ℕ) = 14 := rfl
@[local simp] private theorem localPort15_val : ((15 : Fin 20) : ℕ) = 15 := rfl
@[local simp] private theorem localPort16_val : ((16 : Fin 20) : ℕ) = 16 := rfl
@[local simp] private theorem localPort17_val : ((17 : Fin 20) : ℕ) = 17 := rfl
@[local simp] private theorem localPort18_val : ((18 : Fin 20) : ℕ) = 18 := rfl
@[local simp] private theorem localPort19_val : ((19 : Fin 20) : ℕ) = 19 := rfl
@[local simp] private theorem workPort22_val : ((22 : Fin 42) : ℕ) = 22 := rfl
@[local simp] private theorem workPort23_val : ((23 : Fin 42) : ℕ) = 23 := rfl
@[local simp] private theorem workPort24_val : ((24 : Fin 42) : ℕ) = 24 := rfl
@[local simp] private theorem workPort25_val : ((25 : Fin 42) : ℕ) = 25 := rfl
@[local simp] private theorem workPort26_val : ((26 : Fin 42) : ℕ) = 26 := rfl
@[local simp] private theorem workPort27_val : ((27 : Fin 42) : ℕ) = 27 := rfl
@[local simp] private theorem workPort28_val : ((28 : Fin 42) : ℕ) = 28 := rfl
@[local simp] private theorem workPort29_val : ((29 : Fin 42) : ℕ) = 29 := rfl
@[local simp] private theorem workPort30_val : ((30 : Fin 42) : ℕ) = 30 := rfl
@[local simp] private theorem workPort31_val : ((31 : Fin 42) : ℕ) = 31 := rfl
@[local simp] private theorem workPort32_val : ((32 : Fin 42) : ℕ) = 32 := rfl
@[local simp] private theorem workPort33_val : ((33 : Fin 42) : ℕ) = 33 := rfl
@[local simp] private theorem workPort34_val : ((34 : Fin 42) : ℕ) = 34 := rfl
@[local simp] private theorem workPort35_val : ((35 : Fin 42) : ℕ) = 35 := rfl
@[local simp] private theorem workPort36_val : ((36 : Fin 42) : ℕ) = 36 := rfl
@[local simp] private theorem workPort37_val : ((37 : Fin 42) : ℕ) = 37 := rfl
@[local simp] private theorem workPort38_val : ((38 : Fin 42) : ℕ) = 38 := rfl
@[local simp] private theorem workPort39_val : ((39 : Fin 42) : ℕ) = 39 := rfl
@[local simp] private theorem workPort40_val : ((40 : Fin 42) : ℕ) = 40 := rfl
@[local simp] private theorem workPort41_val : ((41 : Fin 42) : ℕ) = 41 := rfl


def matrixRegisters (i : Fin 8) : Fin 24 := ⟨i.val, by omega⟩
def matrixStacks (i : Fin 20) : Fin 42 := ⟨22 + i.val, by omega⟩

theorem matrixRegisters_injective : Function.Injective matrixRegisters := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun z : Fin 24 => z.val) h

theorem matrixStacks_injective : Function.Injective matrixStacks := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [matrixStacks] at hv
  omega

@[local simp] private theorem matrixStacks_eq_30 (i : Fin 20) :
    matrixStacks i = (30 : Fin 42) ↔ i = 8 :=
  matrixStacks_injective.eq_iff' (a := i) (b := 8) rfl

@[local simp] private theorem matrixStacks_eq_33 (i : Fin 20) :
    matrixStacks i = (33 : Fin 42) ↔ i = 11 :=
  matrixStacks_injective.eq_iff' (a := i) (b := 11) rfl

@[local simp] private theorem matrixStacks_eq_34 (i : Fin 20) :
    matrixStacks i = (34 : Fin 42) ↔ i = 12 :=
  matrixStacks_injective.eq_iff' (a := i) (b := 12) rfl

@[local simp] private theorem matrixStacks_eq_37 (i : Fin 20) :
    matrixStacks i = (37 : Fin 42) ↔ i = 15 :=
  matrixStacks_injective.eq_iff' (a := i) (b := 15) rfl

@[local simp] private theorem matrixStacks_eq_40 (i : Fin 20) :
    matrixStacks i = (40 : Fin 42) ↔ i = 18 :=
  matrixStacks_injective.eq_iff' (a := i) (b := 18) rfl

abbrev matrixPair : Cmd 24 42 :=
  .call (ProgramLinking.liftProgram MatrixPairProgram.program matrixRegisters matrixStacks)

/-- A proof-state embedding, not an executed data transformation. The
relocated instruction table reads and writes the physical ports directly. -/
noncomputable def install (base : StructuredProgram.State 24 42)
    (localState : StructuredProgram.State 8 20) : StructuredProgram.State 24 42 :=
  embedState matrixRegisters matrixStacks base localState

theorem install_stack (base : StructuredProgram.State 24 42)
    (localState : StructuredProgram.State 8 20) (i : Fin 20) :
    (install base localState).stacks (matrixStacks i) = localState.stacks i :=
  embedState_stack _ _ _ _ matrixStacks_injective _

theorem install_register (base : StructuredProgram.State 24 42)
    (localState : StructuredProgram.State 8 20) (i : Fin 8) :
    (install base localState).regs (matrixRegisters i) = localState.regs i :=
  embedState_register _ _ _ _ matrixRegisters_injective _

theorem install_register_frame (base : StructuredProgram.State 24 42)
    (localState : StructuredProgram.State 8 20) (j : Fin 24) (hj : 8 ≤ j.val) :
    (install base localState).regs j = base.regs j := by
  apply embedState_register_frame
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  simp only [matrixRegisters] at hv
  omega

theorem install_stack_frame (base : StructuredProgram.State 24 42)
    (localState : StructuredProgram.State 8 20) (j : Fin 42) (hj : j.val < 22) :
    (install base localState).stacks j = base.stacks j := by
  apply embedState_stack_frame
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  simp only [matrixStacks] at hv
  omega

/-- Every execution premise is a trace of the concrete two-product program. -/
theorem matrixPair_eval (base : StructuredProgram.State 24 42)
    {a b : StructuredProgram.State 8 20} {n : ℕ}
    (h : Trace MatrixPairProgram.program n
      (a.withPC (some MatrixPairProgram.program.entry)) (b.withPC none)) :
    Eval matrixPair n (install base a) (install base b) :=
  eval_call_lifted MatrixPairProgram.program matrixRegisters matrixStacks base
    matrixRegisters_injective matrixStacks_injective h

theorem install_eq (base : StructuredProgram.State 24 42)
    (localState : StructuredProgram.State 8 20)
    (hr : ∀ i, localState.regs i = base.regs (matrixRegisters i))
    (hs : ∀ i, localState.stacks i = base.stacks (matrixStacks i)) :
    install base localState = base := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext j
    change (install base localState).regs j = base.regs j
    by_cases hj : j.val < 8
    · let i : Fin 8 := ⟨j.val, hj⟩
      have hi : matrixRegisters i = j := Fin.ext rfl
      rw [← hi, install_register, hr]
    · exact install_register_frame _ _ j (by omega)
  · funext j
    change (install base localState).stacks j = base.stacks j
    by_cases hj : j.val < 22
    · exact install_stack_frame _ _ j hj
    · let i : Fin 20 := ⟨j.val - 22, by omega⟩
      have hi : matrixStacks i = j := by apply Fin.ext; dsimp [matrixStacks, i]; omega
      rw [← hi, install_stack, hs]

theorem prepared_eq_install (p : ℕ) [Fact p.Prime] {m N : ℕ}
    (M : Fin m → Fin N → ZMod p) (C : Fin N → Fin N → ZMod p)
    (x : Fin N → ZMod p) (split tail : List Bool) (base : StructuredProgram.State 24 42)
    (hentry : BlockSearchLoop.CoefficientEntry (context p M) (tableBits p C) split base) :
    let a := BlockCoefficientAssembly.prepared
      (RecordPrograms.state BlockSearchLoop.coefficientPorts.toPorts
        base false true false tail (MatrixProgramSupport.words (vectorWords p x)).reverse)
    install a (MatrixEncodedProgram.initial p M C x (fun i => a.regs (matrixRegisters i))) = a := by
  dsimp only
  apply install_eq
  · intro i; rfl
  · rcases hentry with ⟨h27, h36, h38, h39, h10, h41, h8, h9, hwork⟩
    intro i
    fin_cases i <;>
      simp [MatrixEncodedProgram.initial, MatrixPairProgram.wide,
        MatrixScalarProgram.scalarStacks, matrixStacks,
        BlockCoefficientAssembly.prepared, BlockCoefficientAssembly.transferState,
        BlockCoefficientFrames.copyState, StackRoutines.copyStacks, StackRoutines.transferStacks,
        RecordPrograms.state, BlockSearchLoop.coefficientPorts, context,
        h27, h36, h38, h39, h10, h41, hwork]

theorem installed_final_stacks (p : ℕ) [Fact p.Prime] {m N : ℕ}
    (M : Fin m → Fin N → ZMod p) (C : Fin N → Fin N → ZMod p)
    (x : Fin N → ZMod p) (base : StructuredProgram.State 24 42)
    (ri rf : Fin 8 → Bool) :
    (install base (MatrixEncodedProgram.final p M C x rf)).stacks =
      BlockCoefficientAssembly.matrixStacks
        (install base (MatrixEncodedProgram.initial p M C x ri)).stacks
        (vectorWords p (BlockSearch.matrixMap C x)) (vectorWords p x)
        (vectorWords p (BlockSearch.matrixMap M (BlockSearch.matrixMap C x))) := by
  funext j
  by_cases hj : j.val < 22
  · have h30 : j ≠ 30 := by intro h; subst j; change 30 < 22 at hj; omega
    have h33 : j ≠ 33 := by intro h; subst j; change 33 < 22 at hj; omega
    have h34 : j ≠ 34 := by intro h; subst j; change 34 < 22 at hj; omega
    have h37 : j ≠ 37 := by intro h; subst j; change 37 < 22 at hj; omega
    have h40 : j ≠ 40 := by intro h; subst j; change 40 < 22 at hj; omega
    simp only [BlockCoefficientAssembly.matrixStacks, Function.update_of_ne h30,
      Function.update_of_ne h33, Function.update_of_ne h34, Function.update_of_ne h37,
      Function.update_of_ne h40, install_stack_frame _ _ _ hj]
  · let i : Fin 20 := ⟨j.val - 22, by omega⟩
    have hi : matrixStacks i = j := by apply Fin.ext; dsimp [matrixStacks, i]; omega
    rw [← hi, install_stack]
    clear_value i
    fin_cases i <;>
      simp [BlockCoefficientAssembly.matrixStacks, Function.update_apply, install_stack,
        MatrixEncodedProgram.initial, MatrixEncodedProgram.final, MatrixPairProgram.wide,
        MatrixScalarProgram.scalarStacks,
        MatrixZeroSemantics.frames_eq_words]

/-- The actual arithmetic command satisfies the state effect needed by the
coefficient iterator. The only premises are the encoded inputs and ordinary
prime-field data; its execution is supplied by the two-product trace. -/
theorem coefficient_matrix_eval (p : ℕ) [Fact p.Prime] {m N : ℕ}
    (M : Fin m → Fin N → ZMod p) (C : Fin N → Fin N → ZMod p)
    (x : Fin N → ZMod p) (split tail : List Bool) (base : StructuredProgram.State 24 42)
    (hentry : BlockSearchLoop.CoefficientEntry (context p M) (tableBits p C) split base) :
    let a := BlockCoefficientAssembly.prepared
      (RecordPrograms.state BlockSearchLoop.coefficientPorts.toPorts
        base false true false tail (MatrixProgramSupport.words (vectorWords p x)).reverse)
    ∃ n b, n ≤ MatrixPairProgram.budget m N (MatrixWordEncoding.width p) ∧
      Eval matrixPair n a b ∧
      b.stacks = BlockCoefficientAssembly.matrixStacks a.stacks
        (vectorWords p (BlockSearch.matrixMap C x)) (vectorWords p x)
        (vectorWords p (BlockSearch.matrixMap M (BlockSearch.matrixMap C x))) ∧
      BlockCoefficientAssembly.ParentFrame a b := by
  dsimp only
  let a := BlockCoefficientAssembly.prepared
    (RecordPrograms.state BlockSearchLoop.coefficientPorts.toPorts
      base false true false tail (MatrixProgramSupport.words (vectorWords p x)).reverse)
  let ri : Fin 8 → Bool := fun i => a.regs (matrixRegisters i)
  obtain ⟨n, hn, rf, ht⟩ := MatrixEncodedProgram.program_trace p M C x ri
  have hstart : install a (MatrixEncodedProgram.initial p M C x ri) = a :=
    prepared_eq_install p M C x split tail base hentry
  have he := matrixPair_eval a ht
  rw [hstart] at he
  refine ⟨n, install a (MatrixEncodedProgram.final p M C x rf), hn, he, ?_, ?_⟩
  · rw [installed_final_stacks p M C x a ri rf, hstart]
  · intro j hj _
    exact install_register_frame _ _ j hj

theorem matrixBits_length (p : ℕ) {m N : ℕ} (M : Fin m → Fin N → ZMod p) :
    (matrixBits p M).length = m * (N * (2 * MatrixWordEncoding.width p + 1)) := by
  unfold matrixBits
  rw [← MatrixVectorProgram.matrixWords_eq_words_flatten]
  simpa only [matrixRows_length] using MatrixPairProgram.matrixWords_length
    (matrixRows p M) N (MatrixWordEncoding.width p)
    (fun row hr => ⟨(matrixRows_shape p M row hr).1.symm,
      (matrixRows_shape p M row hr).2⟩)

theorem vectorBits_length (p : ℕ) {N : ℕ} (x : Fin N → ZMod p) :
    (MatrixProgramSupport.words (vectorWords p x)).length =
      N * (2 * MatrixWordEncoding.width p + 1) := by
  simpa only [vectorWords_length] using MatrixProgramSupport.words_length
    (vectorWords p x) (MatrixWordEncoding.width p) (vectorWords_width p x)

theorem callbackCost_le (p : ℕ) [Fact p.Prime] {m N : ℕ}
    (M : Fin m → Fin N → ZMod p) (C : Fin N → Fin N → ZMod p)
    (d : Fin (N + 1)) (x : Fin N → ZMod p) :
    BlockCoefficientAssembly.callbackCost
      (MatrixPairProgram.budget m N (MatrixWordEncoding.width p)) (context p M)
      (tableBits p C) (List.replicate d.val true)
      (MatrixProgramSupport.words (vectorWords p x))
      (vectorWords p (BlockSearch.matrixMap C x)) (vectorWords p x)
      (vectorWords p (BlockSearch.matrixMap M (BlockSearch.matrixMap C x))) ≤
        coefficientCost p m N := by
  have hd : d.val ≤ N := by have := d.isLt; omega
  unfold BlockCoefficientAssembly.callbackCost BlockCoefficientAssembly.suffixCost
  simp only [MatrixZeroSemantics.frames_eq_words, vectorBits_length, tableBits,
    matrixBits_length, context, List.length_replicate]
  exact MatrixPairProgram.callback_bound m N (MatrixWordEncoding.width p) d.val hd

theorem result_eq_test (p : ℕ) [Fact p.Prime] {m N : ℕ}
    (M : Fin m → Fin N → ZMod p) (C : Fin N → Fin N → ZMod p)
    (d : Fin (N + 1)) (test : List Bool → Bool)
    (htest : ∀ x : Fin N → ZMod p,
      test (MatrixProgramSupport.words (vectorWords p x)) =
        BlockSearchProgram.coefficientTest M (BlockSearchEncoding.splitPair d C)
          (BlockSearchEncoding.headCoefficients d x) (BlockSearchEncoding.tailCoefficients d x))
    (x : Fin N → ZMod p) :
    BlockCoefficientAssembly.result (List.replicate d.val true)
      (vectorWords p (BlockSearch.matrixMap C x)) (vectorWords p x)
      (vectorWords p (BlockSearch.matrixMap M (BlockSearch.matrixMap C x))) =
        test (MatrixProgramSupport.words (vectorWords p x)) := by
  rw [htest]
  unfold BlockCoefficientAssembly.result
  simp only [List.length_replicate, vectorWords, MatrixZeroSemantics.zero_encoded_vector,
    BlockSearchTailSemantics.zero_tail_words]
  exact BlockSearchPredicate.classify_eq_coefficientTest M d C x

/-- Full concrete callback contract for the basis search. Arithmetic,
framed zero scans, prefix skipping, classification, and work-buffer cleanup
all execute fixed instruction tables with a common polynomial bound. -/
theorem coefficientContract (p : ℕ) [Fact p.Prime] {m N : ℕ}
    (M : Fin m → Fin N → ZMod p) (C : Fin N → Fin N → ZMod p)
    (d : Fin (N + 1)) (test : List Bool → Bool)
    (htest : ∀ x : Fin N → ZMod p,
      test (MatrixProgramSupport.words (vectorWords p x)) =
        BlockSearchProgram.coefficientTest M (BlockSearchEncoding.splitPair d C)
          (BlockSearchEncoding.headCoefficients d x) (BlockSearchEncoding.tailCoefficients d x)) :
    BlockSearchLoop.CoefficientContract matrixPair (context p M) (tableBits p C)
      (List.replicate d.val true) test (fun _ => coefficientCost p m N) (validCoefficient p N) := by
  intro bits tail base hv hentry
  obtain ⟨x, rfl⟩ := hv
  have hmatrix := coefficient_matrix_eval p M C x (List.replicate d.val true) tail base hentry
  obtain ⟨n, next, hn, hs, hr, he⟩ := BlockCoefficientAssembly.coefficient_eval
    matrixPair (context p M) (tableBits p C) (List.replicate d.val true)
    (MatrixProgramSupport.words (vectorWords p x)) tail base hentry
    (vectorWords p (BlockSearch.matrixMap C x)) (vectorWords p x)
    (vectorWords p (BlockSearch.matrixMap M (BlockSearch.matrixMap C x)))
    (by simp only [List.length_replicate, vectorWords_length]; have := d.isLt; omega)
    (MatrixPairProgram.budget m N (MatrixWordEncoding.width p)) hmatrix
  rw [result_eq_test p M C d test htest x] at he
  exact ⟨n, next, hn.trans (callbackCost_le p M C d x), hs, hr, he⟩

end SubexponentialSAT.Subexp.BlockCoefficientProgram

end OAI.Algorithms
