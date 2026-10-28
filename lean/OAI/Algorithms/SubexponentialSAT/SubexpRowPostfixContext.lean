import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRowPolynomialCalls
import OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixFrames

namespace OAI.Algorithms

/-! Stored arithmetic data for the row interpreter. Readiness is stated on
the fixed context alone, and proved invariant when source, operand, and
temporary argument ports change. No arithmetic trace is assumed here. -/

namespace SubexponentialSAT.SubexpRowPostfixContext

open BitProgram StructuredCalls
open SubexpLiftRing SubexpQuarticRing
open SubexpConvolutionControl (Store bufferPorts)
open SubexpRowPostfixInterpreter (physicalCfg contextStore)
open SubexpRowArithmeticRelocation (bank)

def operandStore (context : Fin 252 → List Bool) (code depth operands : List Bool) : Store :=
  (physicalCfg (l := 1) none false false false code depth operands context).stacks

def preparedStore (context : Fin 252 → List Bool)
    (code depth operands left right tail : List Bool) : Store :=
  SubexpRowPostfixServices.prepared (operandStore context code depth operands) left right tail

theorem operandStore_frame (context : Fin 252 → List Bool)
    (code depth operands : List Bool) (i : Fin 256)
    (h26 : i ≠ 26) (h28 : i ≠ 28) (h27 : i ≠ 27) :
    operandStore context code depth operands i = contextStore context i :=
  SubexpRowPostfixInterpreter.physicalCfg_frame _ _ _ _ _ _ _ _ _ h26 h28 h27

theorem preparedStore_frame (context : Fin 252 → List Bool)
    (code depth operands left right tail : List Bool) (i : Fin 256)
    (h26 : i ≠ 26) (h28 : i ≠ 28) (h27 : i ≠ 27) (h240 : i ≠ 240) (h241 : i ≠ 241) :
    preparedStore context code depth operands left right tail i = contextStore context i := by
  simp only [preparedStore, SubexpRowPostfixServices.prepared, Function.update_apply,
    h240, h241, h27, ite_false]
  exact operandStore_frame context code depth operands i h26 h28 h27

private theorem bank_ne_fixed {i j : Fin 256} (hj : bank j = j) (h : i ≠ j) : bank i ≠ j :=
  fun he => h (bank.injective (he.trans hj.symm))

theorem preparedStore_bank_frame (context : Fin 252 → List Bool)
    (code depth operands left right tail : List Bool) (i : Fin 256)
    (h26 : i ≠ 26) (h28 : i ≠ 28) (h27 : i ≠ 27) (h240 : i ≠ 240) (h241 : i ≠ 241) :
    preparedStore context code depth operands left right tail (bank i) = contextStore context (bank i) :=
  preparedStore_frame context code depth operands left right tail (bank i)
    (bank_ne_fixed rfl h26) (bank_ne_fixed rfl h28) (bank_ne_fixed rfl h27)
    (bank_ne_fixed rfl h240) (bank_ne_fixed rfl h241)

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

/-- All entries describe literal stored words or empty scratch buffers.
The protected source cache is unrestricted. -/
structure Ready (t z : SubexpRowPolynomialCalls.Coefficient p μ) (D : ℕ)
    (width : List Bool) (frame : Fin 6 → List Bool) (context : Fin 252 → List Bool) : Prop where
  positiveWidth : 0 < baseWidth p μ
  widthLength : width.length = baseWidth p μ
  empty21 : contextStore context 21 = []
  empty99 : contextStore context 99 = []
  empty120 : contextStore context 120 = []
  empty121 : contextStore context 121 = []
  empty122 : contextStore context 122 = []
  empty240 : contextStore context 240 = []
  empty241 : contextStore context 241 = []
  empty244 : contextStore context 244 = []
  empty245 : contextStore context 245 = []
  addStore : ∀ i, contextStore context (SubexpPolynomialAddService.ports i) =
    (DensePolynomialLoop.ready (fun _ => false) M.bits [] [] width [] frame).stacks i
  mulStore : SubexpConvolutionPairSpec.BaseReady p μ M (contextStore context ∘ bank) t width frame
  emptyBuffers : ∀ i, contextStore context (bank (bufferPorts i)) = []
  zeroArray : contextStore context 242 = SubexpRowPolynomialCalls.encode (List.replicate D z)
  dimension : (contextStore context 243).length = D

omit [Fact (Nat.Prime p)] in
theorem Ready.prepared_addStore {t z : SubexpRowPolynomialCalls.Coefficient p μ} {D : ℕ}
    {width : List Bool} {frame : Fin 6 → List Bool} {context : Fin 252 → List Bool}
    (H : Ready p μ M t z D width frame context)
    (code depth operands left right tail : List Bool) :
    ∀ i, preparedStore context code depth operands left right tail
        (SubexpPolynomialAddService.ports i) =
      (DensePolynomialLoop.ready (fun _ => false) M.bits [] [] width [] frame).stacks i := by
  intro i
  rw [preparedStore_frame]
  · exact H.addStore i
  all_goals
    intro h
    have hv := congrArg Fin.val h
    change i.val = _ at hv
    have hi := i.isLt
    omega

omit [Fact (Nat.Prime p)] in
theorem Ready.prepared_mulStore {t z : SubexpRowPolynomialCalls.Coefficient p μ} {D : ℕ}
    {width : List Bool} {frame : Fin 6 → List Bool} {context : Fin 252 → List Bool}
    (H : Ready p μ M t z D width frame context)
    (code depth operands left right tail : List Bool) :
    SubexpConvolutionPairSpec.BaseReady p μ M
      (preparedStore context code depth operands left right tail ∘ bank) t width frame := by
  constructor
  · intro j h70 h71
    change preparedStore context code depth operands left right tail
      (bank (SubexpConvolutionPair.highPort j)) = _
    rw [preparedStore_bank_frame]
    · exact H.mulStore.high j h70 h71
    all_goals
      intro h
      have hv := congrArg Fin.val h
      change 128 + j.val = _ at hv
      have hj := j.isLt
      omega
  · intro i
    change preparedStore context code depth operands left right tail
      (bank (SubexpConvolutionPair.lowPort (SubexpJetCellProgram.scalarPorts i))) = _
    rw [preparedStore_bank_frame]
    · exact H.mulStore.low i
    all_goals
      intro h
      have hv := congrArg Fin.val h
      change i.val = _ at hv
      have hi := i.isLt
      omega
  · change (preparedStore context code depth operands left right tail (bank 104)).length = _
    rw [preparedStore_bank_frame _ _ _ _ _ _ _ 104 (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact H.mulStore.width
  · exact H.widthLength
  · intro j hlo hhi
    change preparedStore context code depth operands left right tail (bank j) = []
    rw [preparedStore_bank_frame]
    · exact H.mulStore.work j hlo hhi
    all_goals
      intro h
      have hv := congrArg Fin.val h
      omega

omit [Fact (Nat.Prime p)] in
theorem Ready.prepared_emptyBuffers {t z : SubexpRowPolynomialCalls.Coefficient p μ} {D : ℕ}
    {width : List Bool} {frame : Fin 6 → List Bool} {context : Fin 252 → List Bool}
    (H : Ready p μ M t z D width frame context)
    (code depth operands left right tail : List Bool) :
    ∀ i, (preparedStore context code depth operands left right tail ∘ bank) (bufferPorts i) = [] := by
  intro i
  change preparedStore context code depth operands left right tail (bank (bufferPorts i)) = []
  rw [preparedStore_bank_frame]
  · exact H.emptyBuffers i
  all_goals fin_cases i <;> decide

end SubexponentialSAT.SubexpRowPostfixContext

end OAI.Algorithms
