import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixVectorProgram

namespace OAI.Algorithms

/-! The two actual matrix products used by the full-basis coefficient checker. -/

namespace SubexponentialSAT.Subexp.MatrixPairProgram

open BitProgram StructuredCalls BinaryArithmetic
open MatrixProgramSupport MatrixScalarProgram MatrixVectorProgram

-- Closed port projections are kept explicit so simplification does not leave
-- dependent branches over the numeral instances for `Fin 20`.
@[local simp] private theorem port0_val : ((0 : Fin 20) : ℕ) = 0 := rfl
@[local simp] private theorem port1_val : ((1 : Fin 20) : ℕ) = 1 := rfl
@[local simp] private theorem port2_val : ((2 : Fin 20) : ℕ) = 2 := rfl
@[local simp] private theorem port3_val : ((3 : Fin 20) : ℕ) = 3 := rfl
@[local simp] private theorem port4_val : ((4 : Fin 20) : ℕ) = 4 := rfl
@[local simp] private theorem port5_val : ((5 : Fin 20) : ℕ) = 5 := rfl
@[local simp] private theorem port6_val : ((6 : Fin 20) : ℕ) = 6 := rfl
@[local simp] private theorem port7_val : ((7 : Fin 20) : ℕ) = 7 := rfl
@[local simp] private theorem port8_val : ((8 : Fin 20) : ℕ) = 8 := rfl
@[local simp] private theorem port9_val : ((9 : Fin 20) : ℕ) = 9 := rfl
@[local simp] private theorem port10_val : ((10 : Fin 20) : ℕ) = 10 := rfl
@[local simp] private theorem port11_val : ((11 : Fin 20) : ℕ) = 11 := rfl
@[local simp] private theorem port12_val : ((12 : Fin 20) : ℕ) = 12 := rfl
@[local simp] private theorem port13_val : ((13 : Fin 20) : ℕ) = 13 := rfl
@[local simp] private theorem port14_val : ((14 : Fin 20) : ℕ) = 14 := rfl
@[local simp] private theorem port15_val : ((15 : Fin 20) : ℕ) = 15 := rfl
@[local simp] private theorem port16_val : ((16 : Fin 20) : ℕ) = 16 := rfl
@[local simp] private theorem port17_val : ((17 : Fin 20) : ℕ) = 17 := rfl
@[local simp] private theorem port18_val : ((18 : Fin 20) : ℕ) = 18 := rfl
@[local simp] private theorem port19_val : ((19 : Fin 20) : ℕ) = 19 := rfl


def corePort (i : Fin 16) : Fin 20 := ⟨i.val, by omega⟩

theorem corePort_injective : Function.Injective corePort := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun z : Fin 20 => z.val) h

def wide (d : MatrixScalarProgram.Data) (matrix count coeff candidate : List Bool) :
    StructuredProgram.State 8 20 :=
  ⟨d.regs, fun j => if h : j.val < 16 then d.stacks ⟨j.val, h⟩
    else if j = 16 then matrix else if j = 17 then count
    else if j = 18 then coeff else candidate⟩

private theorem outside_core (j : Fin 20) (hj : 16 ≤ j.val) : ¬ ∃ i, corePort i = j := by
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  simp only [corePort] at hv
  omega

private theorem embed_core (d base : MatrixScalarProgram.Data)
    (matrix count coeff candidate : List Bool) :
    embedState id corePort (wide base matrix count coeff candidate) d =
      wide d matrix count coeff candidate := by
  apply data_ext
  · simp [embedState, wide]
  · funext j
    by_cases hj : j.val < 16
    · let i : Fin 16 := ⟨j.val, hj⟩
      have hi : corePort i = j := Fin.ext rfl
      rw [← hi, embedState_stack _ _ _ _ corePort_injective]
      simp [wide, corePort]
    · rw [embedState_stack_frame _ _ _ _ j (outside_core j (by omega))]
      simp [wide, hj]

abbrev matrixCall : Cmd 8 20 :=
  .call (ProgramLinking.liftProgram matrixProgram id corePort)

theorem matrixCall_eval (xs : List (List Bool)) (rows : List (List (List Bool)))
    (B : ℕ) (modulus zero : List Bool)
    (hx : ∀ x ∈ xs, x.length = B)
    (hrows : ∀ ys ∈ rows, xs.length = ys.length ∧ ∀ y ∈ ys, y.length = B)
    (hz : zero.length = B) (hzv : BinaryArithmetic.toNat zero = 0)
    (hml : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B)
    (regs : Fin 8 → Bool) (right matrix count coeff candidate : List Bool) :
    ∃ n ≤ matrixBudget rows.length xs.length B, ∃ regs' results,
      Eval matrixCall n
        (wide (state regs [] [] modulus [] [] (matrixWords rows ++ right) (words xs)
          [] zero (List.replicate rows.length true)) matrix count coeff candidate)
        (wide (state regs' [] [] modulus (words results) [] right (words xs) [] zero [])
          matrix count coeff candidate) ∧
      List.Forall₂ (RowResult (BinaryArithmetic.toNat modulus) B xs) rows results := by
  obtain ⟨n, hn, rf, results, ht, hrel⟩ := matrix_trace xs rows B modulus zero hx hrows
    hz hzv hml hm hcap regs right
  have he := eval_call_lifted matrixProgram id corePort
    (wide (state regs [] [] modulus [] [] (matrixWords rows ++ right) (words xs)
      [] zero (List.replicate rows.length true)) matrix count coeff candidate)
    Function.injective_id corePort_injective ht
  rw [embed_core, embed_core] at he
  exact ⟨n, hn, rf, results, he, hrel⟩

abbrev clearVector : Cmd 8 20 := .call (StackRoutines.clearProgram 12 0 1)

abbrev command : Cmd 8 20 :=
  .seq matrixCall
    (.seq (MatrixProgramSupport.copy 12 18 9)
      (.seq clearVector
        (.seq (move 8 12 9)
          (.seq (MatrixProgramSupport.copy 16 11 9)
            (.seq (MatrixProgramSupport.copy 17 15 9) matrixCall)))))

def program := compiled command 11 8

theorem program_labels : size command + 1 = 754 := by decide

theorem matrixWords_length (rows : List (List (List Bool))) (N B : ℕ)
    (hrows : ∀ ys ∈ rows, ys.length = N ∧ ∀ y ∈ ys, y.length = B) :
    (matrixWords rows).length = rows.length * (N * (2 * B + 1)) := by
  induction rows with
  | nil => simp [matrixWords]
  | cons ys rows ih =>
    have hy := hrows ys (by simp)
    have ht := ih (fun z hz => hrows z (List.mem_cons_of_mem _ hz))
    simp only [matrixWords, List.length_append, words_length ys B hy.2, hy.1, ht,
      List.length_cons]
    ring

/-- Compute `y = C*x` and then `z = M*y`. The source matrix `M`, its
row-count metadata, the original coefficient vector, and caller candidate
backup survive at ports 16, 17, 18, and 19. The results are `y` at 12 and `z`
at 8. Both products use the actual fixed matrix controller above. -/
theorem program_trace (xs : List (List Bool))
    (C M : List (List (List Bool))) (B : ℕ) (modulus zero candidate : List Bool)
    (hx : ∀ x ∈ xs, x.length = B)
    (hC : ∀ ys ∈ C, xs.length = ys.length ∧ ∀ y ∈ ys, y.length = B)
    (hM : ∀ ys ∈ M, xs.length = ys.length ∧ ∀ y ∈ ys, y.length = B)
    (hfull : C.length = xs.length)
    (hz : zero.length = B) (hzv : BinaryArithmetic.toNat zero = 0)
    (hml : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B) (regs : Fin 8 → Bool) :
    ∃ n ≤ budget M.length xs.length B, ∃ regs' ys zs,
      Trace program n
        ((wide (state regs [] [] modulus [] [] (matrixWords C) (words xs)
          [] zero (List.replicate C.length true)) (matrixWords M)
            (List.replicate M.length true) [] candidate).withPC (some program.entry))
        ((wide (state regs' [] [] modulus (words zs) [] [] (words ys) [] zero [])
          (matrixWords M) (List.replicate M.length true) (words xs) candidate).withPC none) ∧
      List.Forall₂ (RowResult (BinaryArithmetic.toNat modulus) B xs) C ys ∧
      List.Forall₂ (RowResult (BinaryArithmetic.toNat modulus) B ys) M zs := by
  obtain ⟨n₁, hn₁, r₁, ys, h₁, hrel₁⟩ := matrixCall_eval xs C B modulus zero hx hC hz hzv
    hml hm hcap regs [] (matrixWords M) (List.replicate M.length true) [] candidate
  simp only [List.append_nil] at h₁
  have hys : ys.length = xs.length := hrel₁.length_eq.symm.trans hfull
  let d₁ := wide (state r₁ [] [] modulus (words ys) [] [] (words xs) [] zero [])
    (matrixWords M) (List.replicate M.length true) [] candidate
  obtain ⟨d₂, h₂, hs₂⟩ := MatrixProgramSupport.copy_eval (12 : Fin 20) 18 9
    (by decide) (by decide) (by decide) d₁ rfl
  have hd₂ : d₂ = wide (state d₂.regs [] [] modulus (words ys) [] [] (words xs) [] zero [])
      (matrixWords M) (List.replicate M.length true) (words xs) candidate := by
    apply data_ext <;> try rfl
    rw [hs₂]
    funext j
    fin_cases j <;> simp [d₁, wide, scalarStacks, StackRoutines.copyStacks]
  rw [hd₂] at h₂
  let d₃ := (⟨readRegs d₂.regs 0 1 none,
    StackRoutines.clearStacks 12 d₂.stacks⟩ : StructuredProgram.State 8 20)
  have h₃ := TupleProgram.clear_eval (12 : Fin 20) (0 : Fin 8) 1 d₂
  have hd₃ : d₃ = wide (state d₃.regs [] [] modulus (words ys) [] [] [] [] zero [])
      (matrixWords M) (List.replicate M.length true) (words xs) candidate := by
    apply data_ext <;> try rfl
    dsimp only [d₃]
    rw [hd₂]
    funext j
    fin_cases j <;> simp [wide, scalarStacks, StackRoutines.clearStacks]
  change Eval clearVector _ d₂ d₃ at h₃
  rw [hd₂, hd₃] at h₃
  obtain ⟨d₄, h₄, hs₄⟩ := move_eval (8 : Fin 20) 12 9
    (by decide) (by decide) (by decide)
    (wide (state d₃.regs [] [] modulus (words ys) [] [] [] [] zero [])
      (matrixWords M) (List.replicate M.length true) (words xs) candidate) rfl rfl
  have hd₄ : d₄ = wide (state d₄.regs [] [] modulus [] [] [] (words ys) [] zero [])
      (matrixWords M) (List.replicate M.length true) (words xs) candidate := by
    apply data_ext <;> try rfl
    rw [hs₄]
    funext j
    fin_cases j <;> simp [wide, scalarStacks]
  rw [hd₄] at h₄
  obtain ⟨d₅, h₅, hs₅⟩ := MatrixProgramSupport.copy_eval (16 : Fin 20) 11 9
    (by decide) (by decide) (by decide)
    (wide (state d₄.regs [] [] modulus [] [] [] (words ys) [] zero [])
      (matrixWords M) (List.replicate M.length true) (words xs) candidate) rfl
  have hd₅ : d₅ = wide (state d₅.regs [] [] modulus [] [] (matrixWords M) (words ys) [] zero [])
      (matrixWords M) (List.replicate M.length true) (words xs) candidate := by
    apply data_ext <;> try rfl
    rw [hs₅]
    funext j
    fin_cases j <;> simp [wide, scalarStacks, StackRoutines.copyStacks]
  rw [hd₅] at h₅
  obtain ⟨d₆, h₆, hs₆⟩ := MatrixProgramSupport.copy_eval (17 : Fin 20) 15 9
    (by decide) (by decide) (by decide)
    (wide (state d₅.regs [] [] modulus [] [] (matrixWords M) (words ys) [] zero [])
      (matrixWords M) (List.replicate M.length true) (words xs) candidate) rfl
  have hd₆ : d₆ = wide (state d₆.regs [] [] modulus [] [] (matrixWords M) (words ys) [] zero
      (List.replicate M.length true)) (matrixWords M) (List.replicate M.length true)
      (words xs) candidate := by
    apply data_ext <;> try rfl
    rw [hs₆]
    funext j
    fin_cases j <;> simp [wide, scalarStacks, StackRoutines.copyStacks]
  rw [hd₆] at h₆
  obtain ⟨n₇, hn₇, r₇, zs, h₇, hrel₇⟩ := matrixCall_eval ys M B modulus zero
    (result_widths hrel₁) (fun row hr => ⟨hys.trans (hM row hr).1, (hM row hr).2⟩)
    hz hzv hml hm hcap d₆.regs [] (matrixWords M) (List.replicate M.length true)
    (words xs) candidate
  simp only [List.append_nil] at h₇
  have he := Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃ (Eval.seq h₄ (Eval.seq h₅ (Eval.seq h₆ h₇)))))
  have hlenx := words_length xs B hx
  have hleny : (words ys).length = xs.length * (2 * B + 1) := by
    rw [words_length ys B (result_widths hrel₁), hys]
  have hlenM := matrixWords_length M xs.length B
    (fun row hr => ⟨(hM row hr).1.symm, (hM row hr).2⟩)
  have ht := compiled_halt_trace he 11 8
  refine ⟨n₁ + (7 * (xs.length * (2 * B + 1)) + 5 +
    (2 * (xs.length * (2 * B + 1)) + 3 +
      (6 * (xs.length * (2 * B + 1)) + 6 +
        (7 * (M.length * (xs.length * (2 * B + 1))) + 5 +
          (7 * M.length + 5 + n₇))))) + 1, ?_, r₇, ys, zs, ?_, hrel₁, hrel₇⟩
  · rw [hfull] at hn₁
    rw [hys] at hn₇
    unfold budget
    omega
  · simpa [program, command, d₁, wide, state, scalarStacks, hlenx, hleny, hlenM,
      List.length_replicate] using ht

theorem program_primitive (xs : List (List Bool))
    (C M : List (List (List Bool))) (B : ℕ) (modulus zero candidate : List Bool)
    (hx : ∀ x ∈ xs, x.length = B)
    (hC : ∀ ys ∈ C, xs.length = ys.length ∧ ∀ y ∈ ys, y.length = B)
    (hM : ∀ ys ∈ M, xs.length = ys.length ∧ ∀ y ∈ ys, y.length = B)
    (hfull : C.length = xs.length)
    (hz : zero.length = B) (hzv : BinaryArithmetic.toNat zero = 0)
    (hml : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B) (regs : Fin 8 → Bool) :
    ∃ regs' ys zs,
      Computation.RunsIn (BitProgram.primitive program).step
        (BitProgram.primitiveOverhead program * budget M.length xs.length B)
        (BitProgram.primitiveCfg program
          ((wide (state regs [] [] modulus [] [] (matrixWords C) (words xs)
            [] zero (List.replicate C.length true)) (matrixWords M)
              (List.replicate M.length true) [] candidate).withPC (some program.entry)))
        (BitProgram.primitiveCfg program
          ((wide (state regs' [] [] modulus (words zs) [] [] (words ys) [] zero [])
            (matrixWords M) (List.replicate M.length true) (words xs) candidate).withPC none)) ∧
      List.Forall₂ (RowResult (BinaryArithmetic.toNat modulus) B xs) C ys ∧
      List.Forall₂ (RowResult (BinaryArithmetic.toNat modulus) B ys) M zs := by
  obtain ⟨n, hn, rf, ys, zs, ht, hy, hz'⟩ := program_trace xs C M B modulus zero candidate
    hx hC hM hfull hz hzv hml hm hcap regs
  exact ⟨rf, ys, zs, BitProgram.primitive_execution program ⟨n, hn, ht⟩, hy, hz'⟩

end SubexponentialSAT.Subexp.MatrixPairProgram

end OAI.Algorithms
