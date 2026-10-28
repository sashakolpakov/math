import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticFlatData
import OAI.Algorithms.SubexponentialSAT.ArithmeticCalls
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms

namespace OAI.Algorithms

/-!
# A fixed-control loop for powers of four-word ring elements

The multiplication parameter is an actual finite instruction table, and its
contract is an instruction trace. The concrete endpoint instantiates this table
with the compiled fixed-width quartic multiplier.
-/

namespace SubexponentialSAT.SubexpQuarticPowerCore

open BitProgram StructuredCalls StackRoutines
open SubexpLiftRing SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Data := StructuredProgram.State 8 83
abbrev Regs := Fin 8 → Bool

def native : Fin 77 ↪ Fin 83 :=
  ⟨Fin.castAdd 6, Fin.castAdd_injective _ _⟩

@[simp] theorem native_val (i : Fin 77) : (native i).val = i.val := rfl
@[simp] theorem native_66 : native 66 = (66 : Fin 83) := rfl
@[simp] theorem native_70 : native 70 = (70 : Fin 83) := rfl
@[simp] theorem native_71 : native 71 = (71 : Fin 83) := rfl
@[simp] theorem native_72 : native 72 = (72 : Fin 83) := rfl
@[simp] theorem native_73 : native 73 = (73 : Fin 83) := rfl
@[simp] theorem native_74 : native 74 = (74 : Fin 83) := rfl
@[simp] theorem native_75 : native 75 = (75 : Fin 83) := rfl

/-- Native multiplication data followed by six caller-owned stacks. -/
def store (localStore : Fin 77 → List Bool)
    (base exponent unit acc counter scratch : List Bool) : Fin 83 → List Bool :=
  fun i => Fin.addCases (m := 77) (n := 6) localStore
    ![base, exponent, unit, acc, counter, scratch] i

@[simp] theorem store_native (localStore : Fin 77 → List Bool)
    (base exponent unit acc counter scratch : List Bool) (i : Fin 77) :
    store localStore base exponent unit acc counter scratch (native i) = localStore i := by
  simp [store, native]

@[simp] theorem store_77 (s : Fin 77 → List Bool) (b e u a c z : List Bool) :
    store s b e u a c z 77 = b := rfl
@[simp] theorem store_78 (s : Fin 77 → List Bool) (b e u a c z : List Bool) :
    store s b e u a c z 78 = e := rfl
@[simp] theorem store_79 (s : Fin 77 → List Bool) (b e u a c z : List Bool) :
    store s b e u a c z 79 = u := rfl
@[simp] theorem store_80 (s : Fin 77 → List Bool) (b e u a c z : List Bool) :
    store s b e u a c z 80 = a := rfl
@[simp] theorem store_81 (s : Fin 77 → List Bool) (b e u a c z : List Bool) :
    store s b e u a c z 81 = c := rfl
@[simp] theorem store_82 (s : Fin 77 → List Bool) (b e u a c z : List Bool) :
    store s b e u a c z 82 = z := rfl

def cleanNative (modulus reduction width : List Bool) : Fin 77 → List Bool :=
  SubexpQuarticFlatMul.bankStore (fun _ => []) modulus reduction width []

def initial {B : ℕ} (r : Regs) (modulus width exponent : List Bool)
    (t a unit : Quad (Word B)) : Data :=
  ⟨r, store (cleanNative modulus (SubexpQuarticFlatMul.flat t) width)
    (SubexpQuarticFlatMul.flat a) exponent (SubexpQuarticFlatMul.flat unit) [] [] []⟩

/-- Exact multiplication-table interface, including preparation and cleanup. -/
abbrev MulSpec {L : ℕ} (table : Program 8 77 L) : Prop :=
  ∀ (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t a b : Quad (Word (baseWidth p μ))) (width : List Bool),
    width.length = baseWidth p μ → ∀ r : Regs,
    ∃ rf : Regs, RunsIn table (400000 * (baseWidth p μ + 1)^2)
      ⟨some table.entry, r, SubexpQuarticFlatMul.initialStore M.bits width t a b⟩
      ⟨none, rf, SubexpQuarticFlatMul.finalStore M.bits width t
        (SubexpPreparedQuartic.binaryMul p μ M t a b).1⟩

abbrev multiply {L : ℕ} (table : Program 8 77 L) : Cmd 8 83 :=
  .call (ProgramLinking.liftProgram table id native)

abbrev clearAt (port : Fin 83) : Cmd 8 83 :=
  .call (clearProgram port 0 1)

def cleared (port : Fin 83) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks port []⟩

theorem clear_eval (port : Fin 83) (d : Data) :
    Eval (clearAt port) (2 * (d.stacks port).length + 3) d (cleared port d) := by
  apply Eval.call
  simpa only [cleared, ListRegisterProgram.Run, StructuredProgram.State.withPC,
    clearStacks] using ListRegisterProgram.clear_run port (0 : Fin 8) 1 d.regs d.stacks

private theorem native_ne (i : Fin 77) (j : Fin 83) (hj : 77 ≤ j.val) : native i ≠ j := by
  intro h
  have hv := congrArg (fun x : Fin 83 => x.val) h
  simp only [native_val] at hv
  omega

private theorem native_update (f : Fin 83 → List Bool) (i j : Fin 77) (v : List Bool) :
    Function.update f (native j) v (native i) =
      Function.update (fun k => f (native k)) j v i := by
  simp only [Function.update_apply, native.injective.eq_iff]

private theorem finalStore_update {B : ℕ} (modulus width : List Bool)
    (t a b result : Quad (Word B)) :
    SubexpQuarticFlatMul.finalStore modulus width t result =
      Function.update (Function.update
        (Function.update (SubexpQuarticFlatMul.initialStore modulus width t a b) 70 []) 71 [])
        72 (SubexpQuarticFlatMul.flat result) := by
  funext j
  by_cases h70 : j = 70
  · subst j; simp [SubexpQuarticFlatMul.initialStore, SubexpQuarticFlatMul.finalStore,
      SubexpQuarticFlatMul.bankStore]
  · by_cases h71 : j = 71
    · subst j; simp [SubexpQuarticFlatMul.initialStore, SubexpQuarticFlatMul.finalStore,
        SubexpQuarticFlatMul.bankStore]
    · by_cases h72 : j = 72
      · subst j; simp [SubexpQuarticFlatMul.initialStore, SubexpQuarticFlatMul.finalStore,
          SubexpQuarticFlatMul.bankStore]
      · simp [SubexpQuarticFlatMul.initialStore, SubexpQuarticFlatMul.finalStore,
          SubexpQuarticFlatMul.bankStore, h70, h71, h72]

def productState (d : Data) (rf : Regs) (result : List Bool) : Data :=
  ⟨rf, Function.update (Function.update (Function.update d.stacks 70 []) 71 []) 72 result⟩

theorem multiply_eval {L : ℕ} (table : Program 8 77 L) (spec : MulSpec table)
    (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t a b : Quad (Word (baseWidth p μ))) (width : List Bool)
    (hw : width.length = baseWidth p μ) (d : Data)
    (hd : ∀ i, d.stacks (native i) = SubexpQuarticFlatMul.initialStore M.bits width t a b i) :
    ∃ n rf, n ≤ 400000 * (baseWidth p μ + 1)^2 ∧
      Eval (multiply table) n d
        (productState d rf (SubexpQuarticFlatMul.flat (SubexpPreparedQuartic.binaryMul p μ M t a b).1)) := by
  obtain ⟨rf, n, hn, ht⟩ := spec p μ M t a b width hw d.regs
  have hs : embedState id native d ⟨d.regs, SubexpQuarticFlatMul.initialStore M.bits width t a b⟩ = d := by
    apply embedState_eq_of_ports id native d d _ Function.injective_id native.injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i, rfl⟩).elim
    · exact hd
    · intro i hi; rfl
  have he : embedState id native d
      ⟨rf, SubexpQuarticFlatMul.finalStore M.bits width t (SubexpPreparedQuartic.binaryMul p μ M t a b).1⟩ =
      productState d rf (SubexpQuarticFlatMul.flat (SubexpPreparedQuartic.binaryMul p μ M t a b).1) := by
    apply embedState_eq_of_ports id native d _ _ Function.injective_id native.injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i, rfl⟩).elim
    · intro i
      rw [finalStore_update M.bits width t a b]
      change Function.update (Function.update (Function.update d.stacks (native 70) [])
        (native 71) []) (native 72) _ (native i) = _
      simp only [native_update]
      simp only [hd]
    · intro i hi
      have h70 : i ≠ 70 := fun h => hi ⟨70, h.symm⟩
      have h71 : i ≠ 71 := fun h => hi ⟨71, h.symm⟩
      have h72 : i ≠ 72 := fun h => hi ⟨72, h.symm⟩
      simp [productState, h70, h71, h72]
  have h := eval_call_lifted table id native d Function.injective_id native.injective
    (a := ⟨d.regs, SubexpQuarticFlatMul.initialStore M.bits width t a b⟩)
    (b := ⟨rf, SubexpQuarticFlatMul.finalStore M.bits width t
      (SubexpPreparedQuartic.binaryMul p μ M t a b).1⟩) ht
  rw [hs, he] at h
  exact ⟨n, rf, hn, h⟩

/-- Two operand copies, one reduced multiplication, and replacement of the
accumulator. All native working stacks are restored. -/
abbrev callback {L : ℕ} (table : Program 8 77 L) : Cmd 8 83 :=
  .seq (ArithmeticCalls.copyAt 77 70 75)
    (.seq (ArithmeticCalls.copyAt 80 71 75)
      (.seq (multiply table)
        (.seq (clearAt 80) (.seq (ArithmeticCalls.copyAt 72 80 75) (clearAt 72)))))

/-- The callback's only final stack change is the accumulator. -/
theorem callback_eval {L : ℕ} (table : Program 8 77 L) (spec : MulSpec table)
    (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t a b : Quad (Word (baseWidth p μ))) (width : List Bool)
    (hw : width.length = baseWidth p μ) (d : Data)
    (hnative : ∀ i, d.stacks (native i) = cleanNative M.bits (SubexpQuarticFlatMul.flat t) width i)
    (ha : d.stacks 77 = SubexpQuarticFlatMul.flat a)
    (hb : d.stacks 80 = SubexpQuarticFlatMul.flat b) :
    ∃ n rf, n ≤ 400200 * (baseWidth p μ + 1)^2 ∧
      Eval (callback table) n d
        ⟨rf, Function.update d.stacks 80
          (SubexpQuarticFlatMul.flat (SubexpPreparedQuartic.binaryMul p μ M t a b).1)⟩ := by
  let B := baseWidth p μ
  let result := (SubexpPreparedQuartic.binaryMul p μ M t a b).1
  have h70 : d.stacks 70 = [] := by simpa [cleanNative, SubexpQuarticFlatMul.bankStore] using hnative 70
  have h71 : d.stacks 71 = [] := by simpa [cleanNative, SubexpQuarticFlatMul.bankStore] using hnative 71
  have h72 : d.stacks 72 = [] := by simpa [cleanNative, SubexpQuarticFlatMul.bankStore] using hnative 72
  have h75 : d.stacks 75 = [] := by simpa [cleanNative, SubexpQuarticFlatMul.bankStore] using hnative 75
  let d₁ := ArithmeticCalls.afterCopy 77 70 d
  let d₂ := ArithmeticCalls.afterCopy 80 71 d₁
  have hc₁ : Eval (ArithmeticCalls.copyAt 77 70 75) (28 * B + 5) d d₁ := by
    have h := ArithmeticCalls.copyAt_eval 77 70 75 d (by decide) (by decide) (by decide) h70 h75
    simpa [ha, SubexpQuarticFlatMul.flat_length, B, ← Nat.mul_assoc] using h
  have hc₂ : Eval (ArithmeticCalls.copyAt 80 71 75) (28 * B + 5) d₁ d₂ := by
    have h := ArithmeticCalls.copyAt_eval 80 71 75 d₁ (by decide) (by decide) (by decide)
      (by simp [d₁, ArithmeticCalls.afterCopy, h71]) (by simp [d₁, ArithmeticCalls.afterCopy, h75])
    simpa [d₂, d₁, ArithmeticCalls.afterCopy, hb, SubexpQuarticFlatMul.flat_length, B,
      ← Nat.mul_assoc] using h
  have hready : ∀ i, d₂.stacks (native i) = SubexpQuarticFlatMul.initialStore M.bits width t a b i := by
    intro i
    change Function.update (Function.update d.stacks (native 70) (d.stacks 77))
      (native 71) (Function.update d.stacks 70 (d.stacks 77) 80) (native i) = _
    simp only [native_update]
    simp only [Function.update_of_ne (by decide : (80 : Fin 83) ≠ 70), hnative, ha, hb]
    rfl
  obtain ⟨nm, rm, hnm, hm⟩ := multiply_eval table spec p μ M t a b width hw d₂ hready
  let d₃ := productState d₂ rm (SubexpQuarticFlatMul.flat result)
  let d₄ := cleared 80 d₃
  let d₅ := ArithmeticCalls.afterCopy 72 80 d₄
  let d₆ := cleared 72 d₅
  have hc₃ : Eval (clearAt 80) (8 * B + 3) d₃ d₄ := by
    have h := clear_eval 80 d₃
    simpa [d₄, cleared, d₃, productState, d₂, d₁, ArithmeticCalls.afterCopy, hb,
      SubexpQuarticFlatMul.flat_length, B, ← Nat.mul_assoc] using h
  have hc₄ : Eval (ArithmeticCalls.copyAt 72 80 75) (28 * B + 5) d₄ d₅ := by
    have h := ArithmeticCalls.copyAt_eval 72 80 75 d₄ (by decide) (by decide) (by decide)
      (by simp [d₄, cleared])
      (by simp [d₄, cleared, d₃, productState, d₂, d₁, ArithmeticCalls.afterCopy, h75])
    simpa [d₅, ArithmeticCalls.afterCopy, d₄, cleared, d₃, productState,
      SubexpQuarticFlatMul.flat_length, B, ← Nat.mul_assoc] using h
  have hc₅ : Eval (clearAt 72) (8 * B + 3) d₅ d₆ := by
    have h := clear_eval 72 d₅
    simpa [d₆, d₅, ArithmeticCalls.afterCopy, d₄, cleared, d₃, productState,
      SubexpQuarticFlatMul.flat_length, B, ← Nat.mul_assoc] using h
  have hfinal : d₆ = (⟨d₆.regs, Function.update d.stacks 80 (SubexpQuarticFlatMul.flat result)⟩ : Data) := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext j
      by_cases hj80 : j = 80
      · subst j; simp [d₆, cleared, d₅, ArithmeticCalls.afterCopy, d₄, d₃, productState]
      · by_cases hj72 : j = 72
        · subst j; simp [d₆, cleared, h72]
        · by_cases hj71 : j = 71
          · subst j; simp [d₆, cleared, d₅, ArithmeticCalls.afterCopy, d₄, d₃, productState, h71]
          · by_cases hj70 : j = 70
            · subst j; simp [d₆, cleared, d₅, ArithmeticCalls.afterCopy, d₄, d₃, productState, h70]
            · simp [d₆, cleared, d₅, ArithmeticCalls.afterCopy, d₄, d₃, productState,
                d₂, d₁, hj80, hj72, hj71, hj70]
  have ht := hc₁.seq (hc₂.seq (hm.seq (hc₃.seq (hc₄.seq hc₅))))
  rw [hfinal] at ht
  refine ⟨_, d₆.regs, ?_, ht⟩
  have hover : 100 * B + 21 ≤ 200 * (B + 1)^2 := by nlinarith [Nat.zero_le (B^2)]
  change nm ≤ 400000 * (B+1)^2 at hnm
  calc
    _ = nm + (100 * B + 21) := by ring
    _ ≤ 400000 * (B+1)^2 + 200 * (B+1)^2 := Nat.add_le_add hnm hover
    _ = 400200 * (B+1)^2 := by ring


def ports : CounterForPrograms.Ports 8 83 where
  register := ⟨fun i => ⟨i.val, by omega⟩, by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin 8 => k.val) h)⟩
  counter := 81
  scratch := 82
  counter_ne_scratch := by decide

/-- Only the accumulator changes outside the two countdown ports. -/
def Invariant (p μ : ℕ) [Fact p.Prime] (c : Fin 4 → ZMod (p^μ))
    (origin : Fin 83 → List Bool) (a : Quad (Word (baseWidth p μ)))
    (i : ℕ) (d : Data) : Prop :=
  ∃ b : Quad (Word (baseWidth p μ)),
    (∀ j : Fin 83, j ≠ 81 → j ≠ 82 →
      d.stacks j = Function.update origin 80 (SubexpQuarticFlatMul.flat b) j) ∧
    quotientDenote c (b.map (wordValue p μ)) =
      quotientDenote c (a.map (wordValue p μ)) ^ i

theorem invariant_stable (p μ : ℕ) [Fact p.Prime] (c : Fin 4 → ZMod (p^μ))
    (origin : Fin 83 → List Bool) (a : Quad (Word (baseWidth p μ))) :
    CounterForPrograms.FrameStable ports (Invariant p μ c origin a) := by
  intro i d e hframe hi
  obtain ⟨b, hb, hv⟩ := hi
  refine ⟨b, ?_, hv⟩
  intro j h81 h82
  exact (hframe j h81 h82).symm.trans (hb j h81 h82)

theorem callback_spec {L : ℕ} (table : Program 8 77 L) (spec : MulSpec table)
    (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (c : Fin 4 → ZMod (p^μ)) (t a : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (width : List Bool) (hw : width.length = baseWidth p μ)
    (origin : Fin 83 → List Bool)
    (hnative : ∀ i, origin (native i) = cleanNative M.bits (SubexpQuarticFlatMul.flat t) width i)
    (ha : origin 77 = SubexpQuarticFlatMul.flat a) :
    CounterForPrograms.BodySpec ports (callback table) (Invariant p μ c origin a)
      (fun _ => 400200 * (baseWidth p μ + 1)^2) := by
  intro i d hi hs _
  obtain ⟨b, hb, hv⟩ := hi
  have hd : ∀ j, d.stacks (native j) = cleanNative M.bits (SubexpQuarticFlatMul.flat t) width j := by
    intro j
    rw [hb (native j) (native_ne j 81 (by decide)) (native_ne j 82 (by decide)),
      Function.update_of_ne (native_ne j 80 (by decide))]
    exact hnative j
  have hda : d.stacks 77 = SubexpQuarticFlatMul.flat a := by
    simpa using (hb 77 (by decide) (by decide)).trans ha
  have hdb : d.stacks 80 = SubexpQuarticFlatMul.flat b := by
    simpa using hb 80 (by decide) (by decide)
  obtain ⟨n, rf, hn, he⟩ := callback_eval table spec p μ M t a b width hw d hd hda hdb
  let result := (SubexpPreparedQuartic.binaryMul p μ M t a b).1
  refine ⟨n, ⟨rf, Function.update d.stacks 80 (SubexpQuarticFlatMul.flat result)⟩,
    hn, he, ?_, ?_, result, ?_, ?_⟩
  · simp [ports]
  · simpa [ports] using hs
  · intro j h81 h82
    by_cases h80 : j = 80
    · subst j; simp
    · simp only [Function.update_of_ne h80]
      simpa [h80] using hb j h81 h82
  · rw [SubexpPreparedQuartic.binaryMul_quotient p μ M c t a b ht, hv, pow_succ']

abbrev command {L : ℕ} (table : Program 8 77 L) : Cmd 8 83 :=
  .seq (ArithmeticCalls.copyAt 79 80 75)
    (.seq (ArithmeticCalls.copyAt 78 81 75)
      (.seq (CounterForPrograms.forCmd ports (callback table)) (clearAt 81)))

abbrev program {L : ℕ} (table : Program 8 77 L) : Program 8 83 (size (command table) + 1) :=
  compiled (command table) 78 80

theorem program_labels {L : ℕ} (table : Program 8 77 L) :
    size (command table) + 1 = L + 84 := by
  simp [size, StructuredProgram.size]
  omega

/-- Polynomial in the numerical exponent, fixed coefficient width, and the
actual length of the binary exponent word, including every copy and cleanup. -/
def runtimeBound (B : ℕ) (exponent : List Bool) : ℕ :=
  BinaryArithmetic.toNat exponent * (400200 * (B + 1)^2) +
    (BinaryArithmetic.toNat exponent + 1) * (16 * exponent.length + 16) +
    28 * B + 9 * exponent.length + 14

theorem command_eval {L : ℕ} (table : Program 8 77 L) (spec : MulSpec table)
    (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (c : Fin 4 → ZMod (p^μ)) (t a unit : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (unit.map (wordValue p μ)) = 1)
    (width : List Bool) (hw : width.length = baseWidth p μ) (d : Data)
    (hnative : ∀ i, d.stacks (native i) = cleanNative M.bits (SubexpQuarticFlatMul.flat t) width i)
    (ha : d.stacks 77 = SubexpQuarticFlatMul.flat a)
    (hunit : d.stacks 79 = SubexpQuarticFlatMul.flat unit)
    (h80 : d.stacks 80 = []) (h81 : d.stacks 81 = []) (h82 : d.stacks 82 = []) :
    ∃ n rf b, Eval (command table) n d
        ⟨rf, Function.update d.stacks 80 (SubexpQuarticFlatMul.flat b)⟩ ∧
      quotientDenote c (b.map (wordValue p μ)) =
        quotientDenote c (a.map (wordValue p μ)) ^ BinaryArithmetic.toNat (d.stacks 78) ∧
      n + 1 ≤ runtimeBound (baseWidth p μ) (d.stacks 78) := by
  let B := baseWidth p μ
  have h75 : d.stacks 75 = [] := by
    simpa [cleanNative, SubexpQuarticFlatMul.bankStore] using hnative 75
  let d₁ := ArithmeticCalls.afterCopy 79 80 d
  let d₂ := ArithmeticCalls.afterCopy 78 81 d₁
  have hc₁ : Eval (ArithmeticCalls.copyAt 79 80 75) (28 * B + 5) d d₁ := by
    have h := ArithmeticCalls.copyAt_eval 79 80 75 d (by decide) (by decide) (by decide) h80 h75
    simpa [hunit, SubexpQuarticFlatMul.flat_length, B, ← Nat.mul_assoc] using h
  have hc₂ : Eval (ArithmeticCalls.copyAt 78 81 75) (7 * (d.stacks 78).length + 5) d₁ d₂ := by
    have h := ArithmeticCalls.copyAt_eval 78 81 75 d₁ (by decide) (by decide) (by decide)
      (by simp [d₁, ArithmeticCalls.afterCopy, h81])
      (by simp [d₁, ArithmeticCalls.afterCopy, h75])
    simpa [d₂, d₁, ArithmeticCalls.afterCopy] using h
  have hi : Invariant p μ c d.stacks a 0 d₂ := by
    refine ⟨unit, ?_, by simpa using hu⟩
    intro j hj81 hj82
    simp [d₂, d₁, ArithmeticCalls.afterCopy, hj81, hunit]
  have hs : d₂.stacks ports.scratch = [] := by
    simp [ports, d₂, d₁, ArithmeticCalls.afterCopy, h82]
  obtain ⟨nl, e, he, hei, _, helen, hes, hn⟩ :=
    CounterForPrograms.for_correct ports (callback table) (Invariant p μ c d.stacks a)
      (fun _ => 400200 * (B+1)^2) (invariant_stable p μ c d.stacks a)
      (callback_spec table spec p μ M c t a ht width hw d.stacks hnative ha) d₂ hs hi
  have hcounter : d₂.stacks ports.counter = d.stacks 78 := by
    simp [ports, d₂, d₁, ArithmeticCalls.afterCopy]
  rw [hcounter] at hei helen hn
  rw [CounterPrograms.value_eq_toNat] at hei hn
  rw [CounterForPrograms.budgetSum_const] at hn
  obtain ⟨b, hb, hv⟩ := hei
  change (e.stacks 81).length = (d.stacks 78).length at helen
  have hlast : Eval (clearAt 81) (2 * (d.stacks 78).length + 3) e (cleared 81 e) := by
    have h := clear_eval 81 e
    simpa only [helen] using h
  have hfinal : cleared 81 e =
      (⟨(cleared 81 e).regs, Function.update d.stacks 80 (SubexpQuarticFlatMul.flat b)⟩ : Data) := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext j
      by_cases hj81 : j = 81
      · subst j; simp [cleared, h81]
      · by_cases hj82 : j = 82
        · subst j; simpa [cleared, ports, h82] using hes
        · simpa [cleared, hj81] using hb j hj81 hj82
  have total := hc₁.seq (hc₂.seq (he.seq hlast))
  rw [hfinal] at total
  refine ⟨_, (cleared 81 e).regs, b, total, hv, ?_⟩
  dsimp [runtimeBound]
  change nl ≤ BinaryArithmetic.toNat (d.stacks 78) * (400200 * (B+1)^2) +
    (BinaryArithmetic.toNat (d.stacks 78)+1) * (16*(d.stacks 78).length+16) at hn
  dsimp [B] at hn ⊢
  omega

/-- The complete fixed controller computes a quotient-ring power while
preserving every source and restoring every workspace stack. -/
theorem run_value {L : ℕ} (table : Program 8 77 L) (spec : MulSpec table)
    (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (c : Fin 4 → ZMod (p^μ)) (t a unit : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (unit.map (wordValue p μ)) = 1)
    (width exponent : List Bool) (hw : width.length = baseWidth p μ) (r : Regs) :
    ∃ rf b, quotientDenote c (b.map (wordValue p μ)) =
        quotientDenote c (a.map (wordValue p μ)) ^ BinaryArithmetic.toNat exponent ∧
      RunsIn (program table) (runtimeBound (baseWidth p μ) exponent)
        ((initial r M.bits width exponent t a unit).withPC (some (program table).entry))
        ((⟨rf, Function.update (initial r M.bits width exponent t a unit).stacks
          80 (SubexpQuarticFlatMul.flat b)⟩ : Data).withPC none) := by
  obtain ⟨n, rf, b, he, hv, hn⟩ := command_eval table spec p μ M c t a unit ht hu width hw
    (initial r M.bits width exponent t a unit)
    (by intro i; simp [initial]) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  refine ⟨rf, b, ?_, n+1, ?_, compiled_halt_trace he 78 80⟩
  · simpa [initial] using hv
  · simpa [initial] using hn

/-- A single common bound on coefficient width, exponent width, and exponent
value gives a cubic bound on the complete instruction trace. -/
theorem runtimeBound_le (B : ℕ) (exponent : List Bool) (W : ℕ)
    (hB : B ≤ W) (hE : exponent.length ≤ W)
    (hN : BinaryArithmetic.toNat exponent ≤ W) :
    runtimeBound B exponent ≤ 500000 * (W + 1)^3 := by
  let V := W + 1
  have hV : 1 ≤ V := by dsimp [V]; omega
  have hB' : (B+1)^2 ≤ V^2 := Nat.pow_le_pow_left (by dsimp [V]; omega) 2
  have hN' : BinaryArithmetic.toNat exponent ≤ V := by dsimp [V]; omega
  have hN'' : BinaryArithmetic.toNat exponent + 1 ≤ V := by dsimp [V]; omega
  have hE' : 16 * exponent.length + 16 ≤ 16 * V := by dsimp [V]; omega
  have h₁ : BinaryArithmetic.toNat exponent * (400200 * (B+1)^2) ≤ 400200 * V^3 := by
    calc
      _ ≤ V * (400200 * V^2) := Nat.mul_le_mul hN' (Nat.mul_le_mul_left _ hB')
      _ = 400200 * V^3 := by ring
  have h₂ : (BinaryArithmetic.toNat exponent + 1) * (16 * exponent.length + 16) ≤ 16 * V^2 := by
    calc
      _ ≤ V * (16 * V) := Nat.mul_le_mul hN'' hE'
      _ = 16 * V^2 := by ring
  have h₃ : 28 * B + 9 * exponent.length + 14 ≤ 51 * V := by dsimp [V]; omega
  have hsq : V ≤ V^2 := by
    simpa only [Nat.mul_one, pow_two] using Nat.mul_le_mul_left V hV
  have hcub : V^2 ≤ V^3 := by
    calc
      V^2 = V^2 * 1 := by omega
      _ ≤ V^2 * V := Nat.mul_le_mul_left (V^2) hV
      _ = V^3 := by ring
  change _ ≤ 500000 * V^3
  calc
    runtimeBound B exponent ≤ 400200 * V^3 + 16 * V^2 + 51 * V := by
      dsimp [runtimeBound]
      omega
    _ ≤ 400200 * V^3 + 16 * V^3 + 51 * V^3 :=
      Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left 16 hcub) _)
        (Nat.mul_le_mul_left 51 (hsq.trans hcub))
    _ ≤ 500000 * V^3 := by omega

abbrev callAt {L S : ℕ} (table : Program 8 77 L) (port : Fin 83 ↪ Fin S) : Cmd 8 S :=
  .call (ProgramLinking.liftProgram (program table) id port)

/-- The complete power program can be placed in any larger fixed stack bank.
Every stack except the assigned output port is preserved, including the frame
outside the 83 ports. -/
theorem callAt_eval {L S : ℕ} (table : Program 8 77 L) (spec : MulSpec table)
    (port : Fin 83 ↪ Fin S)
    (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (c : Fin 4 → ZMod (p^μ)) (t a unit : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (unit.map (wordValue p μ)) = 1)
    (width : List Bool) (hw : width.length = baseWidth p μ)
    (d : StructuredProgram.State 8 S)
    (hnative : ∀ i, d.stacks (port (native i)) =
      cleanNative M.bits (SubexpQuarticFlatMul.flat t) width i)
    (ha : d.stacks (port 77) = SubexpQuarticFlatMul.flat a)
    (hunit : d.stacks (port 79) = SubexpQuarticFlatMul.flat unit)
    (h80 : d.stacks (port 80) = []) (h81 : d.stacks (port 81) = [])
    (h82 : d.stacks (port 82) = []) :
    ∃ n rf b, Eval (callAt table port) n d
        ⟨rf, Function.update d.stacks (port 80) (SubexpQuarticFlatMul.flat b)⟩ ∧
      quotientDenote c (b.map (wordValue p μ)) =
        quotientDenote c (a.map (wordValue p μ)) ^ BinaryArithmetic.toNat (d.stacks (port 78)) ∧
      n ≤ runtimeBound (baseWidth p μ) (d.stacks (port 78)) := by
  let localData : Data := ⟨d.regs, fun i => d.stacks (port i)⟩
  obtain ⟨n, rf, b, he, hv, hn⟩ := command_eval table spec p μ M c t a unit ht hu width hw localData
    hnative ha hunit h80 h81 h82
  have hs : embedState id port d localData = d := by
    apply embedState_eq_of_ports id port d d localData Function.injective_id port.injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i, rfl⟩).elim
    · intro i; rfl
    · intro i hi; rfl
  have hf : embedState id port d
      (⟨rf, Function.update localData.stacks 80 (SubexpQuarticFlatMul.flat b)⟩ : Data) =
      (⟨rf, Function.update d.stacks (port 80) (SubexpQuarticFlatMul.flat b)⟩ :
        StructuredProgram.State 8 S) := by
    apply embedState_eq_of_ports id port d _ _ Function.injective_id port.injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i, rfl⟩).elim
    · intro i
      simp only [Function.update_apply, port.injective.eq_iff]
      rfl
    · intro i hi
      have hne : i ≠ port 80 := fun h => hi ⟨80, h.symm⟩
      simp only [Function.update_of_ne hne]
  have ht := compiled_halt_trace he 78 80
  have hcall := eval_call_lifted (program table) id port d Function.injective_id port.injective
    (a := localData)
    (b := ⟨rf, Function.update localData.stacks 80 (SubexpQuarticFlatMul.flat b)⟩) ht
  rw [hs, hf] at hcall
  exact ⟨n+1, rf, b, hcall, hv, hn⟩


end SubexponentialSAT.SubexpQuarticPowerCore

end OAI.Algorithms
