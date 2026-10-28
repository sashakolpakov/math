import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeInversePrelude
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticFlatInverse

namespace OAI.Algorithms

/-! Actual field-size power followed by compact geometric inversion and
physical seed cleanup. Only native inverse output 214 changes. -/

namespace SubexponentialSAT.SubexpLagrangeInverseCall

open BitProgram StructuredCalls
open SubexpLiftRing SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod Fin.ext_iff

def inverseCall : Code := SubexpQuarticFlatInverse.callAt registers inversePortEmbedding

def command : Code := .seq seed (.seq inverseCall (SubexpConvolutionControl.clear 215))

abbrev program : Program 16 256 (size command + 1) := compiled command 205 214

theorem flat_eq {B : ℕ} (a : Quad (Word B)) :
    SubexpQuarticFlatInverse.flat a = SubexpQuarticFlatMul.flat a := rfl

/-- The inverse's retained input bank before the power seed is installed. -/
def blankInputs {B : ℕ} (modulus width counter : List Bool)
    (t a one : Quad (Word B)) (minusOne : Word B) : SubexpQuarticFlatInverse.Inputs :=
  ⟨modulus, SubexpQuarticFlatMul.flat a, [], SubexpQuarticFlatMul.flat t,
    SubexpQuarticFlatMul.flat one, minusOne.val, width, counter⟩

def InverseReady {B : ℕ} (modulus width counter : List Bool)
    (t a one : Quad (Word B)) (minusOne : Word B) (s : Store) : Prop :=
  ∀ i, s (inversePorts i) =
    SubexpQuarticFlatInverse.emptyStore (blankInputs modulus width counter t a one minusOne) [] i

theorem InverseReady.counter {B : ℕ} {modulus width counter : List Bool}
    {t a one : Quad (Word B)} {minusOne : Word B} {s : Store}
    (h : InverseReady modulus width counter t a one minusOne s) : s 224 = counter := by
  simpa [inversePorts, SubexpQuarticFlatInverse.emptyStore, SubexpQuarticFlatInverse.store,
    blankInputs] using h 88

theorem InverseReady.fresh {B : ℕ} {modulus width counter : List Bool}
    {t a one : Quad (Word B)} {minusOne : Word B} {s : Store}
    (h : InverseReady modulus width counter t a one minusOne s) : s 214 = [] := by
  simpa [inversePorts, SubexpQuarticFlatInverse.emptyStore, SubexpQuarticFlatInverse.store] using h 89

theorem InverseReady.seed_empty {B : ℕ} {modulus width counter : List Bool}
    {t a one : Quad (Word B)} {minusOne : Word B} {s : Store}
    (h : InverseReady modulus width counter t a one minusOne s) : s 215 = [] := by
  simpa [inversePorts, SubexpQuarticFlatInverse.emptyStore, SubexpQuarticFlatInverse.store,
    blankInputs] using h 83

theorem seed_store {B : ℕ} (modulus width counter : List Bool)
    (t a one b : Quad (Word B)) (minusOne : Word B) :
    SubexpQuarticFlatInverse.emptyStore
      (SubexpQuarticFlatInverse.inputs modulus width counter t a b one minusOne) [] =
    Function.update (SubexpQuarticFlatInverse.emptyStore
      (blankInputs modulus width counter t a one minusOne) []) 83 (SubexpQuarticFlatMul.flat b) := by
  funext i
  by_cases hi : i = 83
  · subst i
    simp [SubexpQuarticFlatInverse.emptyStore, SubexpQuarticFlatInverse.store,
      SubexpQuarticFlatInverse.inputs, blankInputs, flat_eq]
  · simp [SubexpQuarticFlatInverse.emptyStore, SubexpQuarticFlatInverse.store,
      SubexpQuarticFlatInverse.inputs, blankInputs, hi, flat_eq]

theorem InverseReady.seeded {B : ℕ} {modulus width counter : List Bool}
    {t a one : Quad (Word B)} {minusOne : Word B} {s : Store}
    (h : InverseReady modulus width counter t a one minusOne s) (b : Quad (Word B)) :
    ∀ i, Function.update s 215 (SubexpQuarticFlatMul.flat b) (inversePorts i) =
      SubexpQuarticFlatInverse.emptyStore
        (SubexpQuarticFlatInverse.inputs modulus width counter t a b one minusOne) [] i := by
  intro i
  rw [seed_store]
  have he : inversePorts i = 215 ↔ i = 83 := by
    change inversePorts i = inversePorts 83 ↔ i = 83
    exact inversePorts_injective.eq_iff
  by_cases hi : i = 83
  · subst i; simp [inversePorts]
  · rw [Function.update_of_ne (he.not.mpr hi), Function.update_of_ne hi]
    exact h i

def runtimeBound (B : ℕ) (exponent counter : List Bool) : ℕ :=
  SubexpQuarticPowerProgram.runtimeBound B exponent +
    SubexpQuarticFlatInverse.runtimeBound B counter + 8 * B + 3

/-- Only the actual field-size exponent and the lifting-precision counter
drive these two fixed programs. The nilpotent-defect premise is derived here. -/
theorem command_correct (p μ : ℕ) [Fact p.Prime] (hμ : 0 < μ)
    (M : SubexpPreparedQuartic.Modulus p μ) (t a one : Quad (Word (baseWidth p μ)))
    (minusOne : Word (baseWidth p μ)) (width exponent counter : List Bool)
    (hw : width.length = baseWidth p μ) (d : Data)
    (hpower : PowerReady M.bits width exponent t a one d.stacks)
    (hinverse : InverseReady M.bits width counter t a one minusOne d.stacks)
    (ht : t.map (wordValue p μ) = reductionData (QuarticSearch.liftedCoefficients p μ))
    (hu : denote p μ one = 1) (hm : wordValue p μ minusOne = -1)
    (he : BinaryArithmetic.toNat exponent = p ^ 4 - 2)
    (hc : CounterPrograms.value counter = μ)
    (ha : SubexpActualRing.rho p μ hμ (denote p μ a) ≠ 0) :
    ∃ n rf result, n ≤ runtimeBound (baseWidth p μ) exponent counter ∧
      Eval command n d ⟨rf, Function.update d.stacks 214 (SubexpQuarticFlatMul.flat result)⟩ ∧
      denote p μ result * denote p μ a = 1 ∧
      (SubexpQuarticFlatMul.flat result).length = 4 * baseWidth p μ := by
  obtain ⟨n, rp, b, hn, hp, hb⟩ := seed_eval p μ M (QuarticSearch.liftedCoefficients p μ)
    t a one width exponent hw d hpower ht hu
  let seeded : Data := ⟨Function.extend registers rp d.regs,
    Function.update d.stacks 215 (SubexpQuarticFlatMul.flat b)⟩
  have hb' : denote p μ b = denote p μ a ^ (p ^ 4 - 2) := by
    rw [← he]
    exact hb
  have hnil : (1 - denote p μ a * denote p μ b) ^ CounterPrograms.value counter = 0 := by
    rw [hb', hc]
    exact defect_nilpotent p μ hμ a ha
  obtain ⟨k, ri, result, hk, hi, hv, hlen⟩ := SubexpQuarticFlatInverse.callAt_correct
    registers inversePortEmbedding p μ M (QuarticSearch.liftedCoefficients p μ)
    t a b one minusOne width counter hw seeded (hinverse.seeded b) ht hu hm hnil
  let inverted : Data := ⟨Function.extend registers ri seeded.regs,
    Function.update seeded.stacks 214 (SubexpQuarticFlatMul.flat result)⟩
  have hclear := SubexpConvolutionControl.clear_eval inverted 215
  have hlength : (inverted.stacks 215).length = 4 * baseWidth p μ := by
    simp [inverted, seeded, SubexpQuarticFlatMul.flat_length]
  have hfinal : (SubexpConvolutionControl.afterClear inverted 215).stacks =
      Function.update d.stacks 214 (SubexpQuarticFlatMul.flat result) := by
    funext j
    by_cases hj : j = 215
    · subst j
      simp [SubexpConvolutionControl.afterClear, inverted, seeded, hpower.seed]
    · by_cases hj214 : j = 214
      · subst j; simp [SubexpConvolutionControl.afterClear, inverted, seeded]
      · simp [SubexpConvolutionControl.afterClear, inverted, seeded, hj, hj214]
  have hall : Eval command (n + (k + (2 * (inverted.stacks 215).length + 3))) d
      (SubexpConvolutionControl.afterClear inverted 215) := hp.seq (hi.seq hclear)
  refine ⟨n + (k + (2 * (inverted.stacks 215).length + 3)),
    (SubexpConvolutionControl.afterClear inverted 215).regs, result, ?_, ?_, hv, ?_⟩
  · rw [hlength]
    unfold runtimeBound
    omega
  · have hstate : SubexpConvolutionControl.afterClear inverted 215 =
        (⟨(SubexpConvolutionControl.afterClear inverted 215).regs,
          Function.update d.stacks 214 (SubexpQuarticFlatMul.flat result)⟩ : Data) :=
      congrArg₂ StructuredProgram.State.mk rfl hfinal
    rw [hstate] at hall
    exact hall
  · exact SubexpQuarticFlatMul.flat_length result

theorem runtimeBound_le (B W : ℕ) (exponent counter : List Bool)
    (hB : B ≤ W) (he : exponent.length ≤ W) (hc : counter.length ≤ W)
    (hpower : BinaryArithmetic.toNat exponent ≤ W) (hcount : CounterPrograms.value counter ≤ W) :
    runtimeBound B exponent counter ≤ 3000000 * (W + 1) ^ 3 := by
  have hp := SubexpQuarticPowerProgram.runtimeBound_le B exponent W hB he hpower
  have hi := SubexpQuarticFlatInverse.runtimeBound_le B counter W hB hc hcount
  have hW : W + 1 ≤ (W + 1)^3 := le_self_pow (by omega) (by decide)
  unfold runtimeBound
  omega

theorem program_trace {n : ℕ} {d e : Data} (h : Eval command n d e) :
    Trace program (n + 1) (d.withPC (some program.entry)) (e.withPC none) :=
  compiled_halt_trace h 205 214

end SubexponentialSAT.SubexpLagrangeInverseCall

end OAI.Algorithms
