import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionController
import OAI.Algorithms.SubexponentialSAT.ExecQuantitativeSparsify

namespace OAI.Algorithms

/-! The canonical bytes are already an ordered input to the same machine.
This is an equality of encodings, not an uncharged sorting/preprocessing step.
The ambient variable count, including unused variables, is unchanged. -/

namespace SubexponentialSAT.SqrtLog.Execution

theorem ordered_canonical_encoding {n : ℕ} (F : SAT.CNF (Fin n)) :
    SubexpOrderedRawPrefix.encode (ExecQuantitativeSparsify.formulaList F) =
      Encoding.encodeCNF F := by
  rw [SubexpOrderedRawPrefix.encode_eq]
  exact ExecQuantitativeSparsify.encodeCNF_formulaList F

theorem ordered_canonical_bits {n : ℕ} (F : SAT.CNF (Fin n)) :
    SubexpOrderedRawPrefix.bitLength (ExecQuantitativeSparsify.formulaList F) =
      Encoding.formulaBitLength F := by
  simp only [SubexpOrderedRawPrefix.bitLength, Encoding.formulaBitLength, ordered_canonical_encoding]

def canonicalExecution {er es n : ℕ} {p : SubexpMainProgram.Phases er es}
    {leaf : SubexpMainProgram.MainCmd er es} {F : SAT.CNF (Fin n)}
    (r : SubexpOrderedRawRuntime.Execution p leaf (ExecQuantitativeSparsify.formulaList F)) :
    SubexpMainController.Execution p leaf F where
  afterPrefix := r.afterPrefix
  prefixSteps := r.prefixSteps
  prefixTrace := by simpa only [ordered_canonical_encoding] using r.prefixTrace
  boot := r.boot
  records := r.records
  test := r.test
  cost := r.cost
  invariant := r.invariant
  validPayload := r.validPayload
  callback := r.callback
  validRecords := r.validRecords
  valid := r.valid
  source := r.source
  payload := r.payload
  correct := by simpa only [ExecQuantitativeSparsify.formulaList_set] using r.correct

theorem canonicalExecution_bound {er es n : ℕ} {p : SubexpMainProgram.Phases er es}
    {leaf : SubexpMainProgram.MainCmd er es} {F : SAT.CNF (Fin n)}
    (r : SubexpOrderedRawRuntime.Execution p leaf (ExecQuantitativeSparsify.formulaList F)) :
    (canonicalExecution r).bound = r.bound := rfl

def OrderedCertificate.toCanonical {er es n : ℕ} {p : SubexpMainProgram.Phases er es}
    {leaf : SubexpMainProgram.MainCmd er es} {F : SAT.CNF (Fin n)} {b : Budget}
    (r : OrderedCertificate p leaf (ExecQuantitativeSparsify.formulaList F) b) :
    CanonicalCertificate p leaf F b where
  run := canonicalExecution r.run
  prefixBound := r.prefixBound
  setupBound := r.setupBound
  sparsifyBound := r.sparsifyBound
  leafCountBound := r.leafCountBound
  payloadBound := r.payloadBound
  leafBound := r.leafBound

end SubexponentialSAT.SqrtLog.Execution

end OAI.Algorithms
