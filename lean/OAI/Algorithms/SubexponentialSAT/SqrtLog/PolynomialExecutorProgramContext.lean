import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramReady
import OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixContext

namespace OAI.Algorithms

/-! Persistent native arithmetic context for the source-row postfix machine.
The dispatcher owns26/27/28; neither coefficient-array service touches them. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (contextStore physicalCfg)
open SubexponentialSAT.SubexpRowPostfixContext (operandStore preparedStore operandStore_frame preparedStore_frame)

structure Ready (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (ops : SubexpSymbolicCost.RingProgram (DensePolynomialProgram.Coeff (baseWidth p t) d))
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (J : ℕ)
    (width : List Bool) (frame : Fin 6 → List Bool) (context : Fin 252 → List Bool) : Prop where
  arithmetic : DensePolynomialProgram.PairSpec.BaseReady p t M cache table (contextStore context) width frame
  empty21 : contextStore context 21 = []
  empty99 : contextStore context 99 = []
  empty121 : contextStore context 121 = []
  empty122 : contextStore context 122 = []
  empty240 : contextStore context 240 = []
  empty241 : contextStore context 241 = []
  empty244 : contextStore context 244 = []
  empty245 : contextStore context 245 = []
  buffers : ∀ i, contextStore context (bufferPorts i) = []
  zeroArray : contextStore context 192 = DensePolynomialProgram.encode (List.replicate J ops.zeroRun.1)
  dimension : (contextStore context 193).length = J
  loaderShape : contextStore context 242 = DensePolynomialProgram.encode (List.replicate J ops.zeroRun.1)

variable {p t : ℕ} [Fact p.Prime]
    {M : SubexpPreparedQuartic.Modulus p t} {cache : RingProgram.ScalarCache p t}
    {d : ℕ} {ops : SubexpSymbolicCost.RingProgram (DensePolynomialProgram.Coeff (baseWidth p t) d)}
    {table : Fin d → Fin d → Fin d → Word (baseWidth p t)} {J : ℕ}
    {width : List Bool} {frame : Fin 6 → List Bool} {context : Fin 252 → List Bool}

/-- The native metadata is invariant under source, operand-stack, and binary
argument changes. This is stronger than the shared all-low-ports frame. -/
theorem Ready.prepared_arithmetic (H : Ready p t M cache ops table J width frame context)
    (code depth operands left right tail : List Bool) :
    DensePolynomialProgram.PairSpec.BaseReady p t M cache table
      (preparedStore context code depth operands left right tail) width frame := by
  constructor
  · intro i h8 h9
    rw [preparedStore_frame]
    · exact H.arithmetic.high i h8 h9
    all_goals fin_cases i <;> decide
  · intro i
    rw [preparedStore_frame]
    · exact H.arithmetic.low i
    all_goals
      intro h
      have hv := congrArg Fin.val h
      change i.val = _ at hv
      have hi := i.isLt
      omega
  · rw [preparedStore_frame _ _ _ _ _ _ _ 104 (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact H.arithmetic.width
  · exact H.arithmetic.scalarWidthLength
  · rw [preparedStore_frame _ _ _ _ _ _ _ 204 (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact H.arithmetic.degreeLength
  · rw [preparedStore_frame _ _ _ _ _ _ _ 120 (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact H.arithmetic.scratch
  · intro i hlo hhi
    rw [preparedStore_frame]
    · exact H.arithmetic.work i hlo hhi
    all_goals intro he; have hv := congrArg Fin.val he; norm_num at hv; omega

theorem Ready.prepared_buffers (H : Ready p t M cache ops table J width frame context)
    (code depth operands left right tail : List Bool) :
    ∀ i, preparedStore context code depth operands left right tail (bufferPorts i) = [] := by
  intro i
  rw [preparedStore_frame]
  · exact H.buffers i
  all_goals fin_cases i <;> decide

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
