import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramPair
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramReady
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionPairSpec
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramLoops

namespace OAI.Algorithms

/-! Discharge the convolution controller's local contract with the concrete
native extension-ring multiply-and-accumulate program. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpConvolutionPairSpec
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem buffers_high (base : Store) (w : Buffers) (j : Fin 32)
    (h8 : j ≠ 8) (h9 : j ≠ 9) :
    buffers base w (RingCall.ports j) = base (RingCall.ports j) := by
  apply buffers_frame
  rintro ⟨i, hi⟩
  have hdis : ∀ (i : Fin 11) (j : Fin 32), j ≠ 8 → j ≠ 9 →
      bufferPorts i ≠ RingCall.ports j := by decide
  exact hdis i j h8 h9 hi

variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {degree : ℕ}
    (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) degree))
    (table : Fin degree → Fin degree → Fin degree → Word (baseWidth p t))

/-- Every varying controller buffer receives the same actual fixed pair
program. The only side condition on the base is its concrete static layout. -/
theorem pairSpec (hB : 0 < baseWidth p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (hmul : ∀ a b, (ops.mulRun a b).1 =
      (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table a b).1)
    (base : Store)
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : BaseReady p t M cache table base scalarWidth frame) (D : ℕ) :
    PairSpec Pair.command base RingProgram.flat
      (fun a b => (ops.addRun a b).1) (fun a b => (ops.mulRun a b).1) D
      (Pair.budget degree (baseWidth p t) D) := by
  intro w a b acc hlen hi hacc ha hb regs
  have hin : (w 3).length < acc.length := by omega
  obtain ⟨earlier, c, rest, hearlier, hrows, hsplit, hnext⟩ :=
    SubexpConvolutionEncoding.encode_addProduct_split RingProgram.flat
      (degree * baseWidth p t) RingProgram.flat_length
      (fun a b => (ops.addRun a b).1) (fun a b => (ops.mulRun a b).1) acc (w 3).length a b hin
  let d : Data := ⟨regs, buffers base w⟩
  have hready : Pair.Ready p t M cache table (buffers base w) a b c earlier rest
      (base 104) (w 3) scalarWidth frame := by
    constructor
    · intro j
      by_cases hj8 : j = 8
      · subst j
        simpa [RingCall.ports,RingCall.port,RingScan.serviceState,RingScan.serviceWorkState,
          RingScan.serviceTapes] using ha
      · by_cases hj9 : j = 9
        · subst j
          simpa [RingCall.ports,RingCall.port,RingScan.serviceState,RingScan.serviceWorkState,
            RingScan.serviceTapes] using hb
        · rw [buffers_high base w j hj8 hj9]
          have hh := H.high j hj8 hj9
          fin_cases j <;> simp_all [RingScan.serviceState,RingScan.serviceWorkState,RingScan.serviceTapes]
    · intro i
      rw [buffers_below base w _ (by
        dsimp [SubexpConvolutionPair.lowPort, SubexpJetCellProgram.scalarPorts]
        have := i.isLt
        omega)]
      exact H.low i
    ·
      rw [buffers_102, hacc]
      exact hsplit
    · exact buffers_103 base w
    · exact hearlier.symm
    · exact buffers_104 base w
    · exact H.width
    · simpa only [H.width] using hrows
    · exact H.scalarWidthLength
    · rw [buffers_frame]
      · exact H.degreeLength
      · intro h
        obtain ⟨i,hi⟩ := h
        fin_cases i <;> simp [bufferPorts] at hi
    · rw [buffers_120]
      exact H.scratch
    · intro j hlo hhi
      rw [buffers_work base w j hlo hhi]
      exact H.work j hlo hhi
  obtain ⟨n,rf,hn,he⟩ := Pair.command_run p t M cache ops table hB hz hadd hmul
    (buffers base w) a b c earlier rest (base 104) (w 3) scalarWidth frame hready regs
  let e : Data := ⟨rf, Function.update (Function.update (Function.update (buffers base w)
    198 []) 199 []) 102 (earlier.flatten ++
      (RingProgram.flat (ops.addRun (ops.mulRun a b).1 c).1 ++ rest))⟩
  have hfinal : e.stacks = buffers base
      (Function.update (Function.update (Function.update w 9 []) 10 []) 2
        (encodeArray RingProgram.flat
          (TruncatedConvolution.addProduct (fun a b => (ops.addRun a b).1) (fun a b => (ops.mulRun a b).1)
            (w 3).length a b acc))) := by
    dsimp only [e]
    rw [buffers_update, buffers_update, buffers_update]
    change Function.update (Function.update (Function.update (buffers base w) 198 []) 199 [])
        102 (earlier.flatten ++
          (RingProgram.flat (ops.addRun (ops.mulRun a b).1 c).1 ++ rest)) =
      Function.update (Function.update (Function.update (buffers base w) 198 []) 199 [])
        102 (encodeArray RingProgram.flat
          (TruncatedConvolution.addProduct (fun a b => (ops.addRun a b).1) (fun a b => (ops.mulRun a b).1)
            (w 3).length a b acc))
    exact congrArg
      (fun record : List Bool =>
        Function.update (Function.update (Function.update (buffers base w) 198 []) 199 [])
          102 record) hnext.symm
  refine ⟨n, e.regs, hn.trans ?_, ?_⟩
  · unfold Pair.budget Cell.eventBudget
    gcongr
  · have heq : e = (⟨e.regs, buffers base
        (Function.update (Function.update (Function.update w 9 []) 10 []) 2
          (encodeArray RingProgram.flat
            (TruncatedConvolution.addProduct (fun a b => (ops.addRun a b).1) (fun a b => (ops.mulRun a b).1)
              (w 3).length a b acc)))⟩ : Data) := by
      apply SubexpScanPrimitives.state_ext
      · rfl
      · exact hfinal
    change Eval Pair.command n (⟨regs,buffers base w⟩ : Data) e at he
    rw [heq] at he
    exact he

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec

end OAI.Algorithms
