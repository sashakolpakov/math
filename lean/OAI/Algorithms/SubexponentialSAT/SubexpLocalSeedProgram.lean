import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLocalConstantProgram
import OAI.Algorithms.SubexponentialSAT.SubexpLocalLinearFactorProgram
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticPowerProgram

namespace OAI.Algorithms

/-!
# Physical preparation of the local CRT Fermat seed

The fixed program extracts the constant cell of the preserved local-factor
array, invokes the actual quartic power program, and builds the padded seed
and negative-seed constants. All four output caches are explicit stack data.
The seed word is existentially returned by the same execution that proves
its value; no arithmetic callback or precomputed seed is assumed.
-/

namespace SubexponentialSAT.SubexpLocalSeedProgram

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing

def registers : Fin 8 ↪ Fin 16 := SubexpLocalLinearFactorProgram.registers

def powerPorts : Fin 83 ↪ Fin 256 :=
  ⟨fun i => ⟨128 + i.val, by omega⟩, by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega⟩

def scalarPower : Code :=
  .call (ProgramLinking.liftProgram SubexpQuarticPowerProgram.program registers powerPorts)

def prepareConstant : Code :=
  .seq SubexpLocalConstantProgram.command (.seq (copy 248 205) (clear 248))

def finishSeed : Code :=
  .seq (SubexpPolynomialConstructor.construct 208 104 227)
    (.seq (copy 208 218)
      (.seq SubexpLocalLinearFactorProgram.scalarNegate
        (.seq (SubexpPolynomialConstructor.construct 219 104 228)
          (.seq (clear 218) (clear 219)))))

def command : Code := .seq prepareConstant (.seq scalarPower finishSeed)
abbrev program : Program 16 256 (size command + 1) := compiled command 240 208

def constantArray (D B : ℕ) (value : List Bool) : List Bool :=
  SubexpLinearFactorProgram.paddedBits B value (List.replicate (4 * B) false) D

def finished (s : Store) (D B : ℕ) (seed negative : List Bool) : Store :=
  Function.update (Function.update s 227 (constantArray D B seed))
    228 (constantArray D B negative)

def prepared (s : Store) (D B : ℕ) (constant seed negative : List Bool) : Store :=
  finished (Function.update (Function.update s 205 constant) 208 seed) D B seed negative

def blankNegation (minusOne modulus width : List Bool) : Fin 24 → List Bool :=
  SubexpQuarticFlatNeg.bankStore (SubexpQuarticFlatNeg.emptyBank minusOne)
    modulus [] width []

def finishBudget (D B : ℕ) : ℕ :=
  25000 * (B + 1)^2 + 440 * (D + 1) * (B + 1) + 44 * B + 11

def runtimeBound (D B : ℕ) (rest exponent : List Bool) : ℕ :=
  SubexpQuarticPowerProgram.runtimeBound B exponent +
    25000 * (B + 1)^2 + 440 * (D + 1) * (B + 1) + 9 * rest.length + 164 * B + 38

theorem flat_eq_encode {B : ℕ} (a : Quad (Word B)) :
    SubexpQuarticFlatMul.flat a = SubexpFlatAdd.encode a := by
  simp [SubexpQuarticFlatMul.flat, SubexpQuarticFlatMul.wordLists,
    FourWordPrograms.flatWords, SubexpFlatAdd.encode, SubexpFlatAdd.flatten,
    SubexpFlatAdd.quadWords, Quad.toFn]

theorem native_below (i : Fin 77) :
    (powerPorts (SubexpQuarticPowerProgram.native i)).val < 205 := by
  change 128 + i.val < 205
  omega

theorem negation_ports_ne (i : Fin 24) :
    SubexpLocalLinearFactorProgram.negatePorts i ≠ 205 ∧
    SubexpLocalLinearFactorProgram.negatePorts i ≠ 208 ∧
    SubexpLocalLinearFactorProgram.negatePorts i ≠ 227 := by
  fin_cases i <;> decide

theorem prepareConstant_run (s : Store) (constant rest : List Bool)
    (harray : s 240 = constant ++ rest) (hwidth : (s 104).length = constant.length)
    (h120 : s 120 = []) (h121 : s 121 = []) (h122 : s 122 = [])
    (h205 : s 205 = []) (h247 : s 247 = []) (h248 : s 248 = []) :
    ExecutesIn prepareConstant (30 * constant.length + 9 * rest.length + 27)
      s (Function.update s 205 constant) := by
  let s₁ := Function.update s 248 constant
  let s₂ := Function.update s₁ 205 constant
  have h₁ := SubexpLocalConstantProgram.command_run s constant rest harray hwidth
    h120 h121 h122 h247 h248
  have h₂ : ExecutesIn (copy 248 205) (7 * constant.length + 5) s₁ s₂ := by
    simpa [s₂, s₁, h205] using copy_run 248 205 s₁
      (by decide) (by decide) (by decide) (by simp [s₁, h120])
  have hout : Function.update s₂ 248 [] = Function.update s 205 constant := by
    funext i
    by_cases hi : i = 248 <;> simp [s₂, s₁, Function.update_apply, hi, h248]
  have h₃ : ExecutesIn (clear 248) (2 * constant.length + 3) s₂
      (Function.update s 205 constant) := by
    have h := clear_run 248 s₂
    rw [hout] at h
    simpa [s₂, s₁] using h
  have h := h₁.seq (h₂.seq h₃)
  convert h using 1
  all_goals first | rfl | ring

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

theorem scalarPower_eval (d : Data)
    (c : Fin 4 → ZMod (p^μ)) (t a unit : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (unit.map (wordValue p μ)) = 1)
    (width : List Bool) (hw : width.length = baseWidth p μ)
    (hnative : ∀ i, d.stacks (powerPorts (SubexpQuarticPowerProgram.native i)) =
      SubexpQuarticPowerProgram.cleanNative M.bits (SubexpFlatAdd.encode t) width i)
    (ha : d.stacks 205 = SubexpFlatAdd.encode a)
    (hunit : d.stacks 207 = SubexpFlatAdd.encode unit)
    (h208 : d.stacks 208 = []) (h209 : d.stacks 209 = []) (h210 : d.stacks 210 = []) :
    ∃ n regs' seed, n ≤ SubexpQuarticPowerProgram.runtimeBound (baseWidth p μ) (d.stacks 206) ∧
      Eval scalarPower n d
        ⟨regs', Function.update d.stacks 208 (SubexpFlatAdd.encode seed)⟩ ∧
      quotientDenote c (seed.map (wordValue p μ)) =
        quotientDenote c (a.map (wordValue p μ)) ^ BinaryArithmetic.toNat (d.stacks 206) := by
  classical
  let localData : SubexpQuarticPowerProgram.Data :=
    ⟨fun i => d.regs (registers i), fun i => d.stacks (powerPorts i)⟩
  obtain ⟨n, rf, seed, he, hv, hn⟩ := SubexpQuarticPowerProgram.command_eval
    p μ M c t a unit ht hu width hw localData
    (by simpa only [localData, flat_eq_encode] using hnative)
    (by
      simpa only [localData, show powerPorts (77 : Fin 83) = 205 by rfl, flat_eq_encode]
        using ha)
    (by
      simpa only [localData, show powerPorts (79 : Fin 83) = 207 by rfl, flat_eq_encode]
        using hunit) h208 h209 h210
  let regs' := Function.extend registers rf d.regs
  have hs : embedState registers powerPorts d localData = d := by
    apply embedState_eq_of_ports registers powerPorts d d localData
      registers.injective powerPorts.injective <;> intros <;> rfl
  have hf : embedState registers powerPorts d
      ⟨rf, Function.update localData.stacks 80 (SubexpQuarticFlatMul.flat seed)⟩ =
      (⟨regs', Function.update d.stacks 208 (SubexpFlatAdd.encode seed)⟩ : Data) := by
    apply embedState_eq_of_ports registers powerPorts d _ _
      registers.injective powerPorts.injective
    · intro i
      exact registers.injective.extend_apply rf d.regs i
    · intro i hi
      exact Function.extend_apply' _ _ _ hi
    · intro i
      change Function.update d.stacks (powerPorts 80) (SubexpFlatAdd.encode seed) (powerPorts i) = _
      simp only [Function.update_apply, powerPorts.injective.eq_iff, flat_eq_encode, localData]
    · intro i hi
      have hne : i ≠ 208 := fun h => hi ⟨80, h.symm⟩
      simp [hne]
  have ht' : Trace SubexpQuarticPowerProgram.program (n + 1)
      (localData.withPC (some SubexpQuarticPowerProgram.program.entry))
      ((⟨rf, Function.update localData.stacks 80 (SubexpQuarticFlatMul.flat seed)⟩ :
        SubexpQuarticPowerProgram.Data).withPC none) := compiled_halt_trace he 78 80
  have hcall := eval_call_lifted SubexpQuarticPowerProgram.program registers powerPorts d
    registers.injective powerPorts.injective (a := localData)
    (b := ⟨rf, Function.update localData.stacks 80 (SubexpQuarticFlatMul.flat seed)⟩) ht'
  rw [hs, hf] at hcall
  exact ⟨n + 1, regs', seed, hn, hcall, hv⟩

omit [Fact p.Prime] in
theorem negation_ready_update (s : Store) (seed : Quad (Word (baseWidth p μ)))
    (minusOne : Word (baseWidth p μ)) (width : List Bool)
    (hbase : ∀ i, s (SubexpLocalLinearFactorProgram.negatePorts i) =
      blankNegation minusOne.val M.bits width i) :
    ∀ i, (Function.update s 218 (SubexpFlatAdd.encode seed))
      (SubexpLocalLinearFactorProgram.negatePorts i) =
        SubexpQuarticFlatNeg.initialStore seed minusOne M.bits width i := by
  intro i
  have h := hbase i
  fin_cases i <;>
    simp [SubexpLocalLinearFactorProgram.negatePorts, blankNegation,
      SubexpQuarticFlatNeg.initialStore, SubexpQuarticFlatNeg.bankStore,
      SubexpQuarticFlatNeg.emptyBank, SubexpLocalLinearFactorProgram.flat_eq_encode] at h ⊢ <;>
      exact h

theorem finishSeed_run (s : Store) (D : ℕ) (seed : Quad (Word (baseWidth p μ)))
    (minusOne : Word (baseWidth p μ)) (width : List Bool)
    (hw : width.length = baseWidth p μ)
    (hneg : ∀ i, s (SubexpLocalLinearFactorProgram.negatePorts i) =
      blankNegation minusOne.val M.bits width i)
    (hseed : s 208 = SubexpFlatAdd.encode seed)
    (hD : s 243 = List.replicate D true)
    (hzero : s 104 = List.replicate (4 * baseWidth p μ) false)
    (h100 : s 100 = []) (h101 : s 101 = []) (h102 : s 102 = [])
    (h107 : s 107 = []) (h108 : s 108 = []) (h120 : s 120 = [])
    (h227 : s 227 = []) (h228 : s 228 = []) (h245 : s 245 = []) :
    ExecutesIn finishSeed (finishBudget D (baseWidth p μ)) s
      (finished s D (baseWidth p μ) (SubexpFlatAdd.encode seed)
        (SubexpFlatAdd.encode (SubexpLocalLinearFactorProgram.negative p μ M minusOne seed))) := by
  let B := baseWidth p μ
  let seedBits := SubexpFlatAdd.encode seed
  let negative := SubexpLocalLinearFactorProgram.negative p μ M minusOne seed
  let negativeBits := SubexpFlatAdd.encode negative
  let s₁ := Function.update s 227 (constantArray D B seedBits)
  let s₂ := Function.update s₁ 218 seedBits
  let s₃ := Function.update s₂ 219 negativeBits
  let s₄ := Function.update s₃ 228 (constantArray D B negativeBits)
  let s₅ := Function.update s₄ 218 []
  have h218 : s 218 = [] := by
    simpa [SubexpLocalLinearFactorProgram.negatePorts, blankNegation,
      SubexpQuarticFlatNeg.bankStore, Fin.coe_ofNat_eq_mod] using hneg 18
  have h219 : s 219 = [] := by
    simpa [SubexpLocalLinearFactorProgram.negatePorts, blankNegation,
      SubexpQuarticFlatNeg.bankStore, Fin.coe_ofNat_eq_mod] using hneg 19
  have h₁ : ExecutesIn (SubexpPolynomialConstructor.construct 208 104 227)
      (220 * (D + 1) * (B + 1)) s s₁ := by
    simpa [s₁, constantArray, seedBits, B, hseed, hzero] using
      SubexpPolynomialConstructor.construct_run s 208 104 227
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        D B (by simp [hseed, B]) (by simp [hzero, B]) hD hzero
        h100 h101 h102 h107 h108 h120 h245 h227
  have h₂ : ExecutesIn (copy 208 218) (28 * B + 5) s₁ s₂ := by
    simpa [s₂, s₁, hseed, h218, seedBits, B, ← Nat.mul_assoc] using
      copy_run 208 218 s₁ (by decide) (by decide) (by decide) (by simp [s₁, h120])
  have hneg₁ : ∀ i, s₁ (SubexpLocalLinearFactorProgram.negatePorts i) =
      blankNegation minusOne.val M.bits width i := by
    intro i
    simpa [s₁, (negation_ports_ne i).2.2] using hneg i
  have h₃ : ExecutesIn SubexpLocalLinearFactorProgram.scalarNegate
      (25000 * (B + 1)^2) s₂ s₃ :=
    SubexpLocalLinearFactorProgram.negate_run p μ M s₂ seed minusOne width hw
      (negation_ready_update p μ M s₁ seed minusOne width hneg₁)
  have h₄ : ExecutesIn (SubexpPolynomialConstructor.construct 219 104 228)
      (220 * (D + 1) * (B + 1)) s₃ s₄ := by
    simpa [s₄, constantArray, negativeBits, B, s₃, s₂, s₁, hzero] using
      SubexpPolynomialConstructor.construct_run s₃ 219 104 228
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        D B (by simp [s₃, negativeBits, B]) (by simp [s₃, s₂, s₁, hzero, B])
        (by simp [s₃, s₂, s₁, hD]) (by simp [s₃, s₂, s₁, hzero, B])
        (by simp [s₃, s₂, s₁, h100]) (by simp [s₃, s₂, s₁, h101])
        (by simp [s₃, s₂, s₁, h102]) (by simp [s₃, s₂, s₁, h107])
        (by simp [s₃, s₂, s₁, h108]) (by simp [s₃, s₂, s₁, h120])
        (by simp [s₃, s₂, s₁, h245]) (by simp [s₃, s₂, s₁, h228])
  have h₅ : ExecutesIn (clear 218) (8 * B + 3) s₄ s₅ := by
    simpa [s₅, s₄, s₃, s₂, seedBits, B, ← Nat.mul_assoc] using clear_run 218 s₄
  have hout : Function.update s₅ 219 [] = finished s D B seedBits negativeBits := by
    funext i
    by_cases h218' : i = 218 <;> by_cases h219' : i = 219 <;>
      simp [s₅, s₄, s₃, s₂, s₁, finished, Function.update_apply, h218', h219', h218, h219]
  have h₆ : ExecutesIn (clear 219) (8 * B + 3) s₅
      (finished s D B seedBits negativeBits) := by
    have h := clear_run 219 s₅
    rw [hout] at h
    simpa [s₅, s₄, s₃, negativeBits, B, ← Nat.mul_assoc] using h
  have h := h₁.seq (h₂.seq (h₃.seq (h₄.seq (h₅.seq h₆))))
  unfold finishBudget
  convert h using 1
  all_goals first | rfl | ring

def workPorts : List (Fin 256) :=
  [100,101,102,107,108,120,121,122,205,208,209,210,227,228,245,247,248]

/-- Concrete runtime inputs and empty work space for the complete seed stage. -/
structure Ready (s : Store) (D : ℕ) (rest : List Bool)
    (t a unit : Quad (Word (baseWidth p μ))) (minusOne : Word (baseWidth p μ))
    (powerWidth negationWidth : List Bool) : Prop where
  powerWidth_length : powerWidth.length = baseWidth p μ
  negationWidth_length : negationWidth.length = baseWidth p μ
  native : ∀ i, s (powerPorts (SubexpQuarticPowerProgram.native i)) =
    SubexpQuarticPowerProgram.cleanNative M.bits (SubexpFlatAdd.encode t) powerWidth i
  unit : s 207 = SubexpFlatAdd.encode unit
  negation : ∀ i, s (SubexpLocalLinearFactorProgram.negatePorts i) =
    blankNegation minusOne.val M.bits negationWidth i
  array : s 240 = SubexpFlatAdd.encode a ++ rest
  dimension : s 243 = List.replicate D true
  zero : s 104 = List.replicate (4 * baseWidth p μ) false
  work : ∀ i ∈ workPorts, s i = []

/-- The seed is returned by the same physical execution that establishes its
decoded power. Its representation need not be chosen independently of regs. -/
theorem command_eval (s : Store) (D : ℕ) (rest : List Bool)
    (c : Fin 4 → ZMod (p^μ)) (t a unit : Quad (Word (baseWidth p μ)))
    (minusOne : Word (baseWidth p μ)) (powerWidth negationWidth : List Bool)
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (unit.map (wordValue p μ)) = 1)
    (H : Ready p μ M s D rest t a unit minusOne powerWidth negationWidth)
    (regs : Fin 16 → Bool) :
    ∃ n regs' seed, n ≤ runtimeBound D (baseWidth p μ) rest (s 206) ∧
      Eval command n ⟨regs, s⟩
        ⟨regs', prepared s D (baseWidth p μ) (SubexpFlatAdd.encode a)
          (SubexpFlatAdd.encode seed)
          (SubexpFlatAdd.encode (SubexpLocalLinearFactorProgram.negative p μ M minusOne seed))⟩ ∧
      quotientDenote c (seed.map (wordValue p μ)) =
        quotientDenote c (a.map (wordValue p μ)) ^ BinaryArithmetic.toNat (s 206) := by
  let s₁ := Function.update s 205 (SubexpFlatAdd.encode a)
  have h₁ := prepareConstant_run s (SubexpFlatAdd.encode a) rest H.array
    (by simp [H.zero]) (H.work 120 (by decide)) (H.work 121 (by decide))
    (H.work 122 (by decide)) (H.work 205 (by decide))
    (H.work 247 (by decide)) (H.work 248 (by decide))
  obtain ⟨n₁, r₁, hn₁, he₁⟩ := h₁ regs
  have hnative₁ : ∀ i, s₁ (powerPorts (SubexpQuarticPowerProgram.native i)) =
      SubexpQuarticPowerProgram.cleanNative M.bits (SubexpFlatAdd.encode t) powerWidth i := by
    intro i
    have hne : powerPorts (SubexpQuarticPowerProgram.native i) ≠ 205 := by
      intro he
      have hi := native_below i
      rw [he] at hi
      norm_num [Fin.coe_ofNat_eq_mod] at hi
    simpa [s₁, hne] using H.native i
  obtain ⟨n₂, r₂, seed, hn₂, he₂, hvalue⟩ := scalarPower_eval p μ M
    (⟨r₁, s₁⟩ : Data) c t a unit ht hu powerWidth H.powerWidth_length hnative₁
    (by simp [s₁]) (by simp [s₁, H.unit])
    (by simpa [s₁] using H.work 208 (by decide))
    (by simpa [s₁] using H.work 209 (by decide))
    (by simpa [s₁] using H.work 210 (by decide))
  let s₂ := Function.update s₁ 208 (SubexpFlatAdd.encode seed)
  have hneg₂ : ∀ i, s₂ (SubexpLocalLinearFactorProgram.negatePorts i) =
      blankNegation minusOne.val M.bits negationWidth i := by
    intro i
    simpa [s₂, s₁, (negation_ports_ne i).1, (negation_ports_ne i).2.1] using H.negation i
  have h₃ := finishSeed_run p μ M s₂ D seed minusOne negationWidth
    H.negationWidth_length hneg₂ (by simp [s₂])
    (by simp [s₂, s₁, H.dimension]) (by simp [s₂, s₁, H.zero])
    (by simpa [s₂, s₁] using H.work 100 (by decide))
    (by simpa [s₂, s₁] using H.work 101 (by decide))
    (by simpa [s₂, s₁] using H.work 102 (by decide))
    (by simpa [s₂, s₁] using H.work 107 (by decide))
    (by simpa [s₂, s₁] using H.work 108 (by decide))
    (by simpa [s₂, s₁] using H.work 120 (by decide))
    (by simpa [s₂, s₁] using H.work 227 (by decide))
    (by simpa [s₂, s₁] using H.work 228 (by decide))
    (by simpa [s₂, s₁] using H.work 245 (by decide))
  obtain ⟨n₃, r₃, hn₃, he₃⟩ := h₃ r₂
  refine ⟨n₁ + (n₂ + n₃), r₃, seed, ?_, he₁.seq (he₂.seq he₃), ?_⟩
  · simp only [SubexpFlatAdd.encode_length] at hn₁
    change n₂ ≤ SubexpQuarticPowerProgram.runtimeBound (baseWidth p μ) (s 206) at hn₂
    unfold finishBudget at hn₃
    unfold runtimeBound
    omega
  · exact hvalue

theorem prepared_frame (s : Store) (D B : ℕ) (constant seed negative : List Bool)
    (i : Fin 256) (h205 : i ≠ 205) (h208 : i ≠ 208) (h227 : i ≠ 227) (h228 : i ≠ 228) :
    prepared s D B constant seed negative i = s i := by
  simp [prepared, finished, h205, h208, h227, h228]

theorem prepared_outputs (s : Store) (D B : ℕ) (constant seed negative : List Bool) :
    prepared s D B constant seed negative 205 = constant ∧
    prepared s D B constant seed negative 208 = seed ∧
    prepared s D B constant seed negative 227 = constantArray D B seed ∧
    prepared s D B constant seed negative 228 = constantArray D B negative := by
  simp [prepared, finished]

theorem constantArray_length (D B : ℕ) (bits : List Bool) (hlen : bits.length = 4 * B) :
    (constantArray D B bits).length = D * (4 * B) :=
  SubexpLinearFactorProgram.paddedBits_length D B bits _ hlen (by simp)

theorem seed_lengths (D : ℕ) (seed : Quad (Word (baseWidth p μ)))
    (minusOne : Word (baseWidth p μ)) :
    (SubexpFlatAdd.encode seed).length = 4 * baseWidth p μ ∧
    (constantArray D (baseWidth p μ) (SubexpFlatAdd.encode seed)).length =
      D * (4 * baseWidth p μ) ∧
    (constantArray D (baseWidth p μ) (SubexpFlatAdd.encode
      (SubexpLocalLinearFactorProgram.negative p μ M minusOne seed))).length =
      D * (4 * baseWidth p μ) := by
  exact ⟨SubexpFlatAdd.encode_length _, constantArray_length _ _ _ (SubexpFlatAdd.encode_length _),
    constantArray_length _ _ _ (SubexpFlatAdd.encode_length _)⟩

omit [Fact p.Prime] in
theorem constantArray_encodes (D : ℕ) (zero seed : Quad (Word (baseWidth p μ)))
    (hz : SubexpFlatAdd.encode zero = List.replicate (4 * baseWidth p μ) false) :
    constantArray D (baseWidth p μ) (SubexpFlatAdd.encode seed) =
      SubexpConvolutionEncoding.encodeArray SubexpFlatAdd.encode
        (SubexpLocalCorrectionAlgebra.padded zero seed zero D) := by
  simpa only [constantArray, hz] using
    (SubexpLinearFactorEncoding.encode_padded SubexpFlatAdd.encode zero seed zero
      (baseWidth p μ) D hz).symm

omit [Fact p.Prime] in
theorem constantArray_denote (D : ℕ) (hD : 0 < D)
    (c : Fin 4 → ZMod (p^μ)) (zero seed : Quad (Word (baseWidth p μ)))
    (hz : quotientDenote c (zero.map (wordValue p μ)) = 0) :
    PolynomialAlgorithm.denote
      ((SubexpLocalCorrectionAlgebra.padded zero seed zero D).map
        (fun a => quotientDenote c (a.map (wordValue p μ)))) =
      Polynomial.C (quotientDenote c (seed.map (wordValue p μ))) := by
  rw [SubexpLocalCorrectionAlgebra.padded_denote
    (fun a : Quad (Word (baseWidth p μ)) => quotientDenote c (a.map (wordValue p μ)))
    zero seed zero hz D]
  simp only [hz, map_zero, mul_zero, add_zero]
  ext k
  cases k <;> simp [Truncation.coeff_trunc, hD]

theorem negative_value (c : Fin 4 → ZMod (p^μ))
    (seed : Quad (Word (baseWidth p μ))) (minusOne : Word (baseWidth p μ))
    (hminus : wordValue p μ minusOne = -1) :
    quotientDenote c ((SubexpLocalLinearFactorProgram.negative p μ M minusOne seed).map
      (wordValue p μ)) = -quotientDenote c (seed.map (wordValue p μ)) :=
  SubexpQuarticNegMachine.negateWords_quotient p μ M minusOne seed hminus c

omit [Fact p.Prime] in
theorem encoded_tail_length (tail : List (Quad (Word (baseWidth p μ)))) :
    ((tail.map SubexpFlatAdd.encode).flatten).length = tail.length * (4 * baseWidth p μ) := by
  induction tail with
  | nil => simp
  | cons a tail ih =>
      simp [ih, Nat.succ_mul, Nat.add_comm] ; ring

theorem runtimeBound_polynomial (D B : ℕ) (rest exponent : List Bool)
    (hrest : rest.length ≤ D * (4 * B)) :
    runtimeBound D B rest exponent + 1 ≤
      SubexpQuarticPowerProgram.runtimeBound B exponent + 26000 * (D + 1) * (B + 1)^2 := by
  have hB : B ≤ (B + 1)^2 := by nlinarith
  have hB1 : B + 1 ≤ (B + 1)^2 := by nlinarith
  have hlinear := Nat.mul_le_mul_left (D + 1) hB1
  have hDB := Nat.mul_le_mul (Nat.le_succ D) hB
  have hsquare : (B + 1)^2 ≤ (D + 1) * (B + 1)^2 :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos D)
  have hsmall : B ≤ (D + 1) * (B + 1)^2 := hB.trans hsquare
  have hone : 1 ≤ (D + 1) * (B + 1)^2 := by
    have : 1 ≤ (B + 1)^2 := by
      exact (by positivity : 0 < (B + 1)^2)
    exact this.trans hsquare
  unfold runtimeBound
  nlinarith

/-- All growing parameters remain explicit: the dimension is separate from
the common bound on coefficient width and the stored exponent's size/value. -/
theorem runtimeBound_le (D B W : ℕ) (rest exponent : List Bool)
    (hrest : rest.length ≤ D * (4 * B)) (hB : B ≤ W)
    (hE : exponent.length ≤ W) (hN : BinaryArithmetic.toNat exponent ≤ W) :
    runtimeBound D B rest exponent + 1 ≤
      (500000 + 26000 * (D + 1)) * (W + 1)^3 := by
  have hpower := SubexpQuarticPowerProgram.runtimeBound_le B exponent W hB hE hN
  have hsquare : (B + 1)^2 ≤ (W + 1)^3 := by
    calc
      (B + 1)^2 ≤ (W + 1)^2 := Nat.pow_le_pow_left (by omega) 2
      _ = (W + 1)^2 * 1 := by ring
      _ ≤ (W + 1)^2 * (W + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = (W + 1)^3 := by ring
  calc
    runtimeBound D B rest exponent + 1 ≤
        SubexpQuarticPowerProgram.runtimeBound B exponent +
          26000 * (D + 1) * (B + 1)^2 := runtimeBound_polynomial D B rest exponent hrest
    _ ≤ 500000 * (W + 1)^3 + 26000 * (D + 1) * (W + 1)^3 :=
      Nat.add_le_add hpower (Nat.mul_le_mul_left _ hsquare)
    _ = (500000 + 26000 * (D + 1)) * (W + 1)^3 := by ring

/-- For a D-cell input array, the whole executed stage has polynomial
overhead beyond the actual scalar power routine, including the final halt. -/
theorem command_typed_eval (s : Store) (D : ℕ)
    (tail : List (Quad (Word (baseWidth p μ)))) (hlen : tail.length + 1 = D)
    (c : Fin 4 → ZMod (p^μ)) (t a unit : Quad (Word (baseWidth p μ)))
    (minusOne : Word (baseWidth p μ)) (powerWidth negationWidth : List Bool)
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (unit.map (wordValue p μ)) = 1)
    (H : Ready p μ M s D ((tail.map SubexpFlatAdd.encode).flatten)
      t a unit minusOne powerWidth negationWidth) (regs : Fin 16 → Bool) :
    ∃ n regs' seed,
      n + 1 ≤ SubexpQuarticPowerProgram.runtimeBound (baseWidth p μ) (s 206) +
        26000 * (D + 1) * (baseWidth p μ + 1)^2 ∧
      Eval command n ⟨regs, s⟩
        ⟨regs', prepared s D (baseWidth p μ) (SubexpFlatAdd.encode a)
          (SubexpFlatAdd.encode seed)
          (SubexpFlatAdd.encode (SubexpLocalLinearFactorProgram.negative p μ M minusOne seed))⟩ ∧
      quotientDenote c (seed.map (wordValue p μ)) =
        quotientDenote c (a.map (wordValue p μ)) ^ BinaryArithmetic.toNat (s 206) := by
  obtain ⟨n, rf, seed, hn, he, hv⟩ := command_eval p μ M s D
    ((tail.map SubexpFlatAdd.encode).flatten) c t a unit minusOne powerWidth negationWidth
    ht hu H regs
  refine ⟨n, rf, seed, (Nat.add_le_add_right hn 1).trans ?_, he, hv⟩
  apply runtimeBound_polynomial
  rw [encoded_tail_length]
  exact Nat.mul_le_mul_right _ (by omega)

theorem program_trace {n : ℕ} {d e : Data} (he : Eval command n d e) :
    Trace program (n + 1) (d.withPC (some program.entry)) (e.withPC none) :=
  compiled_halt_trace he 240 208

theorem program_primitive {n budget : ℕ} {d e : Data}
    (he : Eval command n d e) (hn : n ≤ budget) :
    Computation.RunsIn (primitive program).step (primitiveOverhead program * (budget + 1))
      (primitiveCfg program (d.withPC (some program.entry)))
      (primitiveCfg program (e.withPC none)) := by
  obtain ⟨steps, hsteps, ht⟩ := primitive_trace program (program_trace he)
  exact ⟨steps, hsteps.trans (Nat.mul_le_mul_left _ (by omega)), ht⟩

end SubexponentialSAT.SubexpLocalSeedProgram

end OAI.Algorithms
