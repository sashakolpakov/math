import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSourceRowLayout
import OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixContext
import OAI.Algorithms.SubexponentialSAT.SubexpSourceZero

namespace OAI.Algorithms

/-! The concrete one-time initializer establishes the complete stored-data
contract of the source-row interpreter. No arithmetic execution is assumed. -/

namespace SubexponentialSAT.SubexpSourceRowReady

open BitProgram StructuredCalls
open SubexpLiftRing SubexpQuarticRing
open SubexpRowPostfixInterpreter (contextStore physicalCfg ports)
open SubexpRowArithmeticRelocation (bank)

private theorem zero_array {p : ℕ} (z : SubexpRowPolynomialCalls.Coefficient p 1) (D : ℕ)
    (hz : SubexpFlatAdd.encode z = List.replicate (4 * baseWidth p 1) false) :
    SubexpRowPolynomialCalls.encode (List.replicate D z) =
      List.replicate (D * (4 * baseWidth p 1)) false := by
  induction D with
  | zero => simp [SubexpRowPolynomialCalls.encode, SubexpConvolutionControl.encodeArray]
  | succ D ih =>
      change SubexpFlatAdd.encode z ++ SubexpRowPolynomialCalls.encode (List.replicate D z) = _
      rw [hz, ih, ← List.replicate_add]
      congr 1
      ring

/-- The actual initialized store satisfies every source-row entry guard.
The premises identify the three input cache words and the canonical zero. -/
theorem ready (p : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1)
    (t z : SubexpRowPolynomialCalls.Coefficient p 1) (a : Data)
    (hmodulus : a.stacks 128 = M.bits)
    (hreduction : a.stacks 130 = SubexpQuarticFlatMul.flat t)
    (hwidth : (a.stacks 129).length = baseWidth p 1)
    (hzero : SubexpFlatAdd.encode z = List.replicate (4 * baseWidth p 1) false) :
    SubexpRowPostfixContext.Ready p 1 M t z (SubexpSourceRowContext.dimension a)
      (a.stacks 129) (scalarFrame a) (context a) := by
  constructor
  · simp [baseWidth]
  · exact hwidth
  all_goals rw [contextStore_eq_result]
  case empty21 | empty99 | empty120 | empty121 | empty122 |
      empty240 | empty241 | empty244 | empty245 =>
    exact empty_at a _ (by decide) (by decide) (by decide) (by decide) (by decide)
  case addStore => simpa [hmodulus] using low_layout a
  case mulStore =>
    constructor
    · intro i _ _
      simpa [Function.comp_def, hmodulus, hreduction] using high_layout a i
    · intro i
      change (SubexpSourceRowContext.result a).stacks
        (bank (SubexpPolynomialAddService.ports i)) = _
      rw [SubexpRowArithmeticRelocation.bank_low _ (by
        change i.val < 128
        have := i.isLt
        omega)]
      simpa [hmodulus, DensePolynomialLoop.ready, DensePolynomialLoop.state,
        DensePolynomialLoop.stackArray, SubexpFlatAdd.ready, SubexpFlatAdd.state,
        SubexpFlatAdd.stacks] using low_layout a i
    · simp [SubexpRowArithmeticRelocation.bank_low _ (by decide : (104 : Fin 256).val < 128),
        SubexpSourceRowContext.sourceWidth, hwidth]
    · exact hwidth
    · intro i hlo hhi
      rw [Function.comp_apply, SubexpRowArithmeticRelocation.bank_low i (by omega)]
      have hne (j : Fin 256) (hj : j.val < 112 ∨ 119 < j.val) : i ≠ j := by
        intro heq
        have hv := congrArg (fun x : Fin 256 => x.val) heq
        omega
      exact empty_at a i (by simp only [SubexpSourceRowContext.NeedsClear]; omega)
        ⟨hne 5 (by decide), hne 194 (by decide), hne 10 (by decide),
          hne 202 (by decide), hne 201 (by decide), hne 74 (by decide), hne 248 (by decide)⟩
        (hne 104 (by decide)) (hne 242 (by decide)) (hne 243 (by decide))
  case emptyBuffers =>
    intro i
    fin_cases i
    all_goals
      exact empty_at a _ (by decide) (by decide) (by decide) (by decide) (by decide)
  case zeroArray =>
    rw [zero_array z _ hzero, SubexpSourceRowContext.result_zeroArray]
    simp [SubexpSourceRowContext.sourceWidth, hwidth]
  case dimension => simp

theorem target_width (a : Data) :
    contextStore (context a) 74 = a.stacks SubexpSourceRowContext.targetWidthInput := by
  rw [contextStore_eq_result]
  exact SubexpSourceRowContext.result_word a (SubexpSourceRowContext.targetWidthInput, 74)
    (by simp [SubexpSourceRowContext.copies]) (by decide)

theorem output_empty (a : Data) : contextStore (context a) 87 = [] := by
  rw [contextStore_eq_result]
  exact empty_at a _ (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem bank_lt250 (i : Fin 256) (hi : i.val < 250) : (bank i).val < 250 := by
  change (SubexpRowArithmeticRelocation.bankIndex i).val < 250
  unfold SubexpRowArithmeticRelocation.bankIndex
  split
  · change i.val + 86 < 250
    omega
  · split
    · change i.val - 86 < 250
      omega
    · exact hi

/-- The initializer may read its two input ports through a different Main
mapping. Their ordinary workspace values are irrelevant to row readiness. -/
theorem ready_congr_below250 (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ)
    (t z : SubexpRowPolynomialCalls.Coefficient p μ) (D : ℕ)
    (width : List Bool) (frame : Fin 6 → List Bool)
    (before after : Fin 252 → List Bool)
    (H : SubexpRowPostfixContext.Ready p μ M t z D width frame before)
    (h : ∀ i : Fin 256, i.val < 250 → contextStore after i = contextStore before i) :
    SubexpRowPostfixContext.Ready p μ M t z D width frame after := by
  constructor
  · exact H.positiveWidth
  · exact H.widthLength
  case empty21 => rw [h 21 (by decide)]; exact H.empty21
  case empty99 => rw [h 99 (by decide)]; exact H.empty99
  case empty120 => rw [h 120 (by decide)]; exact H.empty120
  case empty121 => rw [h 121 (by decide)]; exact H.empty121
  case empty122 => rw [h 122 (by decide)]; exact H.empty122
  case empty240 => rw [h 240 (by decide)]; exact H.empty240
  case empty241 => rw [h 241 (by decide)]; exact H.empty241
  case empty244 => rw [h 244 (by decide)]; exact H.empty244
  case empty245 => rw [h 245 (by decide)]; exact H.empty245
  case addStore =>
    intro i
    rw [h _ (by change i.val < 250; have := i.isLt; omega)]
    exact H.addStore i
  case mulStore =>
    constructor
    · intro i h70 h71
      change contextStore after (bank (SubexpConvolutionPair.highPort i)) = _
      rw [h _ (bank_lt250 _ (by change 128 + i.val < 250; have := i.isLt; omega))]
      exact H.mulStore.high i h70 h71
    · intro i
      change contextStore after
        (bank (SubexpConvolutionPair.lowPort (SubexpJetCellProgram.scalarPorts i))) = _
      rw [h _ (bank_lt250 _ (by change i.val < 250; have := i.isLt; omega))]
      exact H.mulStore.low i
    · change (contextStore after (bank 104)).length = _
      rw [h _ (bank_lt250 _ (by decide))]
      exact H.mulStore.width
    · exact H.mulStore.scalarWidthLength
    · intro i hlo hhi
      change contextStore after (bank i) = []
      rw [h _ (bank_lt250 _ (by omega))]
      exact H.mulStore.work i hlo hhi
  case emptyBuffers =>
    intro i
    rw [h _ (bank_lt250 _ (by fin_cases i <;> decide))]
    exact H.emptyBuffers i
  case zeroArray => rw [h 242 (by decide)]; exact H.zeroArray
  case dimension => rw [h 243 (by decide)]; exact H.dimension

end SubexponentialSAT.SubexpSourceRowReady

end OAI.Algorithms
