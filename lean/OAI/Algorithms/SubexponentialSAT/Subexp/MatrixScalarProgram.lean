import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
import OAI.Algorithms.SubexponentialSAT.ModularRingPrograms

namespace OAI.Algorithms

/-!
# Scalar subroutines with the matrix checker's surrounding data preserved

These are calls to the actual finite modular-arithmetic instruction tables.
The eight additional ports carry vector streams, output, and runtime metadata.
-/

namespace SubexponentialSAT.Subexp.MatrixScalarProgram

open BitProgram StructuredCalls BinaryArithmetic ModularRingPrograms
open MatrixProgramSupport

abbrev Data := StructuredProgram.State 8 16

def servicePort (i : Fin 8) : Fin 16 := ⟨i.val, by omega⟩

theorem servicePort_injective : Function.Injective servicePort := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun z : Fin 16 => z.val) h

def scalarStacks (x y modulus acc left right saved output zero input : List Bool) :
    Fin 16 → List Bool :=
  ![x, y, [], [], [], modulus, [], [], acc, [], left, right, saved, output, zero, input]

abbrev state (regs : Fin 8 → Bool)
    (x y modulus acc left right saved output zero input : List Bool) : Data :=
  ⟨regs, scalarStacks x y modulus acc left right saved output zero input⟩

abbrev multiply : Cmd 8 16 :=
  .call (ProgramLinking.liftProgram wordMulProgram id servicePort)

abbrev add : Cmd 8 16 :=
  .call (ProgramLinking.liftProgram wordAddProgram id servicePort)

private theorem outside_service (j : Fin 16) (hj : 8 ≤ j.val) :
    ¬ ∃ i, servicePort i = j := by
  rintro ⟨i, h⟩
  have hv := congrArg Fin.val h
  simp only [servicePort] at hv
  omega

private theorem embed_scalar (regs baseRegs : Fin 8 → Bool)
    (x y modulus acc left right saved output zero input : List Bool) :
    embedState id servicePort (state baseRegs [] [] modulus acc left right saved output zero input)
      ⟨regs, extendSeven (scalarInput x y modulus) []⟩ =
      state regs x y modulus acc left right saved output zero input := by
  apply data_ext
  · simp [embedState ]
  · funext j
    by_cases hj : j.val < 8
    · let i : Fin 8 := ⟨j.val, hj⟩
      have hi : servicePort i = j := Fin.ext rfl
      rw [← hi, embedState_stack _ _ _ _ servicePort_injective]
      clear_value i
      fin_cases i <;> rfl
    · rw [embedState_stack_frame _ _ _ _ j (outside_service j (by omega))]
      fin_cases j <;> simp_all [ scalarStacks ]

theorem multiply_eval (regs : Fin 8 → Bool)
    (x y modulus acc left right saved output zero input : List Bool) (B : ℕ)
    (hx : x.length = B) (hy : y.length = B)
    (hml : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ n ≤ 6000 * (B + 1) ^ 2, ∃ regs' result,
      Eval multiply n (state regs x y modulus acc left right saved output zero input)
        (state regs' result [] modulus acc left right saved output zero input) ∧
      result.length = B ∧ BinaryArithmetic.toNat result = (BinaryArithmetic.toNat x * BinaryArithmetic.toNat y) % BinaryArithmetic.toNat modulus := by
  obtain ⟨regs', result, ⟨n, hn, ht⟩, hl, hv⟩ :=
    wordMul_value regs x y modulus B hx hy hml hm hcap
  have he := eval_call_lifted wordMulProgram id servicePort
    (state regs [] [] modulus acc left right saved output zero input)
    Function.injective_id servicePort_injective
    (a := ⟨regs, extendSeven (scalarInput x y modulus) []⟩)
    (b := ⟨regs', extendSeven (scalarInput result [] modulus) []⟩) ht
  change Eval multiply n
    (embedState id servicePort _ ⟨regs, extendSeven (scalarInput x y modulus) []⟩)
    (embedState id servicePort _ ⟨regs', extendSeven (scalarInput result [] modulus) []⟩) at he
  rw [embed_scalar, embed_scalar] at he
  exact ⟨n, hn, regs', result, he, hl, hv⟩

theorem add_eval (regs : Fin 8 → Bool)
    (x y modulus acc left right saved output zero input : List Bool) (B : ℕ)
    (hx : x.length = B) (hy : y.length = B)
    (hml : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ n ≤ 6000 * (B + 1) ^ 2, ∃ regs' result,
      Eval add n (state regs x y modulus acc left right saved output zero input)
        (state regs' result [] modulus acc left right saved output zero input) ∧
      result.length = B ∧ BinaryArithmetic.toNat result = (BinaryArithmetic.toNat x + BinaryArithmetic.toNat y) % BinaryArithmetic.toNat modulus := by
  obtain ⟨regs', result, ⟨n, hn, ht⟩, hl, hv⟩ :=
    wordAdd_value regs x y modulus B hx hy hml hm hcap
  have he := eval_call_lifted wordAddProgram id servicePort
    (state regs [] [] modulus acc left right saved output zero input)
    Function.injective_id servicePort_injective
    (a := ⟨regs, extendSeven (scalarInput x y modulus) []⟩)
    (b := ⟨regs', extendSeven (scalarInput result [] modulus) []⟩) ht
  change Eval add n
    (embedState id servicePort _ ⟨regs, extendSeven (scalarInput x y modulus) []⟩)
    (embedState id servicePort _ ⟨regs', extendSeven (scalarInput result [] modulus) []⟩) at he
  rw [embed_scalar, embed_scalar] at he
  exact ⟨n, hn, regs', result, he, hl, hv⟩

abbrev accumulate : Cmd 8 16 :=
  .seq multiply (.seq (move 8 1 9) (.seq add (move 0 8 9)))

/-- One genuine modular multiply-add, preserving both vector streams and all
saved caller data. The accumulator is returned on port 8. -/
theorem accumulate_eval (regs : Fin 8 → Bool)
    (x y modulus acc left right saved output zero input : List Bool) (B : ℕ)
    (hx : x.length = B) (hy : y.length = B) (ha : acc.length = B)
    (hml : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ n ≤ 12000 * (B + 1) ^ 2 + 12 * B + 12, ∃ regs' result,
      Eval accumulate n (state regs x y modulus acc left right saved output zero input)
        (state regs' [] [] modulus result left right saved output zero input) ∧
      result.length = B ∧ BinaryArithmetic.toNat result < BinaryArithmetic.toNat modulus ∧
      (BinaryArithmetic.toNat result : ZMod (BinaryArithmetic.toNat modulus)) =
        (BinaryArithmetic.toNat x : ZMod (BinaryArithmetic.toNat modulus)) * (BinaryArithmetic.toNat y : ZMod (BinaryArithmetic.toNat modulus)) +
          (BinaryArithmetic.toNat acc : ZMod (BinaryArithmetic.toNat modulus)) := by
  obtain ⟨n₁, hn₁, r₁, product, h₁, hl₁, hv₁⟩ :=
    multiply_eval regs x y modulus acc left right saved output zero input B hx hy hml hm hcap
  obtain ⟨d₂, h₂, hs₂⟩ := move_eval (8 : Fin 16) 1 9 (by decide) (by decide) (by decide)
    (state r₁ product [] modulus acc left right saved output zero input) rfl rfl
  have hd₂ : d₂ = state d₂.regs product acc modulus [] left right saved output zero input := by
    apply data_ext <;> try rfl
    rw [hs₂]
    funext j
    fin_cases j <;> simp [ scalarStacks]
  rw [hd₂] at h₂
  obtain ⟨n₃, hn₃, r₃, result, h₃, hl₃, hv₃⟩ :=
    add_eval d₂.regs product acc modulus [] left right saved output zero input B hl₁ ha hml hm hcap
  obtain ⟨d₄, h₄, hs₄⟩ := move_eval (0 : Fin 16) 8 9 (by decide) (by decide) (by decide)
    (state r₃ result [] modulus [] left right saved output zero input) rfl rfl
  have hd₄ : d₄ = state d₄.regs [] [] modulus result left right saved output zero input := by
    apply data_ext <;> try rfl
    rw [hs₄]
    funext j
    fin_cases j <;> simp [ scalarStacks]
  rw [hd₄] at h₄
  have he := Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃ h₄))
  refine ⟨n₁ + (6 * B + 6 + (n₃ + (6 * B + 6))), by omega,
    d₄.regs, result, ?_, hl₃, ?_, ?_⟩
  · simpa [accumulate, state, scalarStacks, ha, hl₃] using he
  · rw [hv₃]
    exact Nat.mod_lt _ hm
  · rw [hv₃, ZMod.natCast_mod, Nat.cast_add, hv₁, ZMod.natCast_mod, Nat.cast_mul]

end SubexponentialSAT.Subexp.MatrixScalarProgram

end OAI.Algorithms
