import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticFlatInverseCore
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Flat geometric inversion with charged bank initialization, scalar
execution, packing, and cleanup. The seed is supplied by the caller's
actual Fermat-power stage; the inverse theorem uses its nilpotent defect. -/

namespace SubexponentialSAT.SubexpQuarticFlatInverse

open BitProgram StructuredCalls SubexpScanPrimitives StackRoutines
open SubexpLiftRing SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod

def bankCall : Code := .call (ProgramLinking.liftProgram SubexpInverseProgram.inverseProgram id native)
def command : Code := .seq prepare (.seq bankCall finish)
def program := compiled command 82 89

def runtimeBound (B : ℕ) (counter : List Bool) : ℕ :=
  SubexpInverseProgram.instructionBound B counter.length (CounterPrograms.value counter) +
    2000 * (B + counter.length + 1)

/-- The controller is polynomial in the coefficient width, counter width,
and the actual iteration count. No modulus-sized exponent loop occurs. -/
theorem runtimeBound_le (B : ℕ) (counter : List Bool) (W : ℕ)
    (hB : B ≤ W) (hC : counter.length ≤ W) (hN : CounterPrograms.value counter ≤ W) :
    runtimeBound B counter ≤ 2000000 * (W + 1)^3 := by
  let A := W + 1
  have hBB : (B + 1)^2 ≤ A^2 := by
    have h := Nat.mul_le_mul (Nat.add_le_add_right hB 1) (Nat.add_le_add_right hB 1)
    simpa only [pow_two] using h
  have h12 : A ≤ A^2 := by
    calc
      A ≤ A + W * A := by omega
      _ = A^2 := by dsimp [A]; ring
  have h23 : A^2 ≤ A^3 := by
    calc
      A^2 ≤ A^2 + W * A^2 := by omega
      _ = A^3 := by dsimp [A]; ring
  have hconst : (B + 1)^2 ≤ A^3 := hBB.trans h23
  have hprod : CounterPrograms.value counter * (B + 1)^2 ≤ A^3 := by
    calc
      _ ≤ A * A^2 := Nat.mul_le_mul (by dsimp [A]; omega) hBB
      _ = A^3 := by ring
  have hcontrol : (CounterPrograms.value counter + 1) * (counter.length + 1) ≤ A^3 := by
    calc
      _ ≤ A * A := Nat.mul_le_mul (by dsimp [A]; omega) (by dsimp [A]; omega)
      _ = A^2 := by ring
      _ ≤ A^3 := h23
  have hn : CounterPrograms.value counter ≤ A^3 := by dsimp [A] at *; omega
  have hsum : B + counter.length + 1 ≤ 2 * A^3 := by dsimp [A] at *; omega
  have hpos : 1 ≤ A^3 := Nat.succ_le_of_lt (pow_pos (by dsimp [A]; omega) 3)
  unfold runtimeBound SubexpInverseProgram.instructionBound
  change _ ≤ 2000000 * A^3
  nlinarith only [hconst, hprod, hcontrol, hn, hsum, hpos]

theorem store_native {B : ℕ} (I : Inputs) (bank : Bank B) (count result : List Bool) (i : Fin 82) :
    typedStore I bank count result (native i) =
      SubexpInverseProgram.extendedStacks bank I.modulus count [] i := by
  fin_cases i <;> simp [typedStore, store, native, SubexpInverseProgram.extendedStacks,
    SubexpQuarticMachine.restingState, SubexpQuarticMachine.store,
    SubexpQuarticMachine.scalarWork, Fin.addCases] <;> rfl

theorem embed_bank {B : ℕ} (I : Inputs) (bank frameBank : Bank B)
    (count frameCount result : List Bool) (regs frameRegs : Fin 8 → Bool) :
    embedState id native ⟨frameRegs, typedStore I frameBank frameCount result⟩
      (SubexpInverseProgram.extendedState regs bank I.modulus count []) =
      (⟨regs, typedStore I bank count result⟩ : Data) := by
  apply embedState_eq id native Function.injective_id native.injective
  · intro i; rfl
  · intro i; exact store_native I bank count result i
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i hi
    have hn : 82 ≤ i.val := by
      by_contra h
      exact hi ⟨⟨i.val, by omega⟩, Fin.ext rfl⟩
    have h71 : ¬ i.val < 71 := by omega
    have h80 : i ≠ 80 := by intro h; subst i; norm_num at hn
    simp [typedStore, store, h71, h80]

theorem bankCall_eval (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (I : Inputs) (hmod : I.modulus = M.bits) (bank : Bank (baseWidth p μ))
    (counter : List Bool) (regs : Fin 8 → Bool) :
    ∃ n rf count, n ≤ SubexpInverseProgram.instructionBound
        (baseWidth p μ) counter.length (CounterPrograms.value counter) ∧
      Eval bankCall n ⟨regs, typedStore I bank counter []⟩
        ⟨rf, typedStore I (SubexpInverseProgram.runBank p μ M (CounterPrograms.value counter) bank) count []⟩ ∧
      count.length = counter.length := by
  obtain ⟨rf, count, ⟨n, hn, ht⟩, _, hl⟩ := SubexpInverseProgram.inverse_execute p μ M regs bank counter
  have he := eval_call_lifted SubexpInverseProgram.inverseProgram id native
    (⟨regs, typedStore I bank counter []⟩ : Data) Function.injective_id native.injective ht
  rw [← hmod, embed_bank, embed_bank] at he
  exact ⟨n, rf, count, hn, he, hl⟩

def inverseWords (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t a b unit : Quad (Word (baseWidth p μ))) (minusOne : Word (baseWidth p μ))
    (counter : List Bool) : Quad (Word (baseWidth p μ)) :=
  output (SubexpInverseProgram.runBank p μ M (CounterPrograms.value counter)
    (initialBank t a b unit minusOne))

/-- Complete physical execution from flat inputs. Every temporary bank word
is initialized and eventually cleared; the counter input is copied. -/
theorem command_eval (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t a b unit : Quad (Word (baseWidth p μ))) (minusOne : Word (baseWidth p μ))
    (width counter : List Bool) (hw : width.length = baseWidth p μ) (regs : Fin 8 → Bool) :
    ∃ n rf, n + 1 ≤ runtimeBound (baseWidth p μ) counter ∧
      Eval command n
        ⟨regs, emptyStore (inputs M.bits width counter t a b unit minusOne) []⟩
        ⟨rf, emptyStore (inputs M.bits width counter t a b unit minusOne)
          (flat (inverseWords p μ M t a b unit minusOne counter))⟩ := by
  let I := inputs M.bits width counter t a b unit minusOne
  obtain ⟨rp, hp⟩ := prepare_eval M.bits width counter t a b unit minusOne hw regs
  obtain ⟨n, rb, count, hn, he, hl⟩ := bankCall_eval p μ M I rfl
    (initialBank t a b unit minusOne) counter rp
  have hf := finish_eval I
    (SubexpInverseProgram.runBank p μ M (CounterPrograms.value counter)
      (initialBank t a b unit minusOne)) count rb
  refine ⟨(881 * baseWidth p μ + 7 * counter.length + 634) +
      (n + (170 * baseWidth p μ + 2 * count.length + 239)), readRegs rb 0 1 none, ?_,
    hp.seq (he.seq hf)⟩
  unfold runtimeBound
  rw [hl]
  omega

theorem initialBank_spec {B : ℕ} (t a b one : Quad (Word B)) (minusOne : Word B) :
    SubexpInverseProgram.reduction (initialBank t a b one minusOne) = t ∧
    SubexpInverseProgram.left (initialBank t a b one minusOne) = a ∧
    SubexpInverseProgram.right (initialBank t a b one minusOne) = b ∧
    SubexpInverseProgram.unit (initialBank t a b one minusOne) = one ∧
    initialBank t a b one minusOne 69 = minusOne ∧
    initialBank t a b one minusOne 70 = zeroWord B := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem zeroWord_value (p μ : ℕ) : wordValue p μ (zeroWord (baseWidth p μ)) = 0 := by
  simp [wordValue, zeroWord, toNat_fixedBits]

theorem initialBank_constants (p μ : ℕ) [Fact p.Prime]
    (c : Fin 4 → ZMod (p^μ)) (t a b one : Quad (Word (baseWidth p μ)))
    (minusOne : Word (baseWidth p μ))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (one.map (wordValue p μ)) = 1)
    (hm : wordValue p μ minusOne = -1) :
    SubexpInverseProgram.Constants p μ c (initialBank t a b one minusOne) := by
  obtain ⟨hr, _, _, ho, hn, hz⟩ := initialBank_spec t a b one minusOne
  unfold SubexpInverseProgram.Constants SubexpInverseProgram.denoteQuad
  rw [hr, ho, hn, hz]
  exact ⟨ht, hu, hm, zeroWord_value p μ⟩

theorem inverseWords_value (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (c : Fin 4 → ZMod (p^μ)) (t a b one : Quad (Word (baseWidth p μ)))
    (minusOne : Word (baseWidth p μ)) (counter : List Bool)
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (one.map (wordValue p μ)) = 1)
    (hm : wordValue p μ minusOne = -1) :
    quotientDenote c ((inverseWords p μ M t a b one minusOne counter).map (wordValue p μ)) =
      NilpotentDefect.geometricInverse (quotientDenote c (a.map (wordValue p μ)))
        (quotientDenote c (b.map (wordValue p μ))) (CounterPrograms.value counter) := by
  have h := SubexpInverseProgram.runBank_denote p μ M c (initialBank t a b one minusOne)
    (initialBank_constants p μ c t a b one minusOne ht hu hm) (CounterPrograms.value counter)
  obtain ⟨_, ha, hb, _, _, _⟩ := initialBank_spec t a b one minusOne
  simpa only [SubexpInverseProgram.denoteQuad, ha, hb, inverseWords, output] using h

theorem inverseWords_correct (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (c : Fin 4 → ZMod (p^μ)) (t a b one : Quad (Word (baseWidth p μ)))
    (minusOne : Word (baseWidth p μ)) (counter : List Bool)
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (one.map (wordValue p μ)) = 1)
    (hm : wordValue p μ minusOne = -1)
    (hnil : (1 - quotientDenote c (a.map (wordValue p μ)) *
      quotientDenote c (b.map (wordValue p μ))) ^ CounterPrograms.value counter = 0) :
    quotientDenote c ((inverseWords p μ M t a b one minusOne counter).map (wordValue p μ)) *
      quotientDenote c (a.map (wordValue p μ)) = 1 := by
  rw [inverseWords_value p μ M c t a b one minusOne counter ht hu hm]
  exact NilpotentDefect.geometricInverse_mul _ _ _ hnil

theorem emptyStore_result (I : Inputs) (result : List Bool) :
    emptyStore I result = Function.update (emptyStore I []) 89 result := by
  funext i
  by_cases hi : i = 89
  · subst i; simp [emptyStore, store]
  · simp [emptyStore, store, hi]

abbrev callAt {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 96 ↪ Fin s) : Cmd r s :=
  .call (ProgramLinking.liftProgram program registers ports)

private theorem extend_agree {α β γ : Type*} (f : α ↪ β) (values : α → γ)
    (frame : β → γ) (h : ∀ i, frame (f i) = values i) : Function.extend f values frame = frame := by
  classical
  funext j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [f.injective.extend_apply, h]
  · exact Function.extend_apply' _ _ _ hj

/-- Static wiring into an arbitrary larger controller preserves every
stack except the chosen result port. The register frame is explicit. -/
theorem callAt_eval {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 96 ↪ Fin s)
    (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t a b one : Quad (Word (baseWidth p μ))) (minusOne : Word (baseWidth p μ))
    (width counter : List Bool) (hw : width.length = baseWidth p μ) (d : State r s)
    (hstore : ∀ i, d.stacks (ports i) = emptyStore (inputs M.bits width counter t a b one minusOne) [] i) :
    ∃ n rf, n ≤ runtimeBound (baseWidth p μ) counter ∧ Eval (callAt registers ports) n d
      ⟨Function.extend registers rf d.regs, Function.update d.stacks (ports 89)
        (flat (inverseWords p μ M t a b one minusOne counter))⟩ := by
  obtain ⟨n, rf, hn, he⟩ := command_eval p μ M t a b one minusOne width counter hw
    (d.regs ∘ registers)
  have ht := compiled_halt_trace he 82 89
  let I := inputs M.bits width counter t a b one minusOne
  have hsi : Function.extend ports (emptyStore I []) d.stacks = d.stacks :=
    extend_agree ports _ _ hstore
  have hri : Function.extend registers (d.regs ∘ registers) d.regs = d.regs :=
    extend_agree registers _ _ (fun _ => rfl)
  have hso : Function.extend ports
      (emptyStore I (flat (inverseWords p μ M t a b one minusOne counter))) d.stacks =
      Function.update d.stacks (ports 89) (flat (inverseWords p μ M t a b one minusOne counter)) := by
    rw [emptyStore_result, ProgramLinking.extend_update ports.injective, hsi]
  have hl := eval_call_lifted program registers ports d registers.injective ports.injective ht
  change Eval (callAt registers ports) (n + 1)
    (⟨Function.extend registers (d.regs ∘ registers) d.regs,
      Function.extend ports (emptyStore I []) d.stacks⟩ : State r s)
    ⟨Function.extend registers rf d.regs,
      Function.extend ports
        (emptyStore I (flat (inverseWords p μ M t a b one minusOne counter))) d.stacks⟩ at hl
  rw [hri, hsi, hso] at hl
  refine ⟨n + 1, rf, hn, ?_⟩
  exact hl

theorem callAt_correct {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 96 ↪ Fin s)
    (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (c : Fin 4 → ZMod (p^μ)) (t a b one : Quad (Word (baseWidth p μ)))
    (minusOne : Word (baseWidth p μ)) (width counter : List Bool)
    (hw : width.length = baseWidth p μ) (d : State r s)
    (hstore : ∀ i, d.stacks (ports i) = emptyStore (inputs M.bits width counter t a b one minusOne) [] i)
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (one.map (wordValue p μ)) = 1)
    (hm : wordValue p μ minusOne = -1)
    (hnil : (1 - quotientDenote c (a.map (wordValue p μ)) *
      quotientDenote c (b.map (wordValue p μ))) ^ CounterPrograms.value counter = 0) :
    ∃ n rf result, n ≤ runtimeBound (baseWidth p μ) counter ∧
      Eval (callAt registers ports) n d
        ⟨Function.extend registers rf d.regs, Function.update d.stacks (ports 89) (flat result)⟩ ∧
      quotientDenote c (result.map (wordValue p μ)) * quotientDenote c (a.map (wordValue p μ)) = 1 ∧
      (flat result).length = 4 * baseWidth p μ := by
  obtain ⟨n, rf, hn, he⟩ := callAt_eval registers ports p μ M t a b one minusOne width counter hw d hstore
  exact ⟨n, rf, inverseWords p μ M t a b one minusOne counter, hn, he,
    inverseWords_correct p μ M c t a b one minusOne counter ht hu hm hnil, flat_length _⟩

theorem program_trace {n : ℕ} {d e : Data} (he : Eval command n d e) :
    Trace program (n + 1) (d.withPC (some program.entry)) (e.withPC none) := compiled_halt_trace he 82 89

theorem program_primitive {n bound : ℕ} {d e : Data} (he : Eval command n d e) (hn : n + 1 ≤ bound) :
    Computation.RunsIn (primitive program).step (primitiveOverhead program * bound)
      (primitiveCfg program (d.withPC (some program.entry)))
      (primitiveCfg program (e.withPC none)) := by
  obtain ⟨steps, hs, ht⟩ := primitive_trace program (program_trace he)
  exact ⟨steps, hs.trans (Nat.mul_le_mul_left _ hn), ht⟩

end SubexponentialSAT.SubexpQuarticFlatInverse

end OAI.Algorithms
