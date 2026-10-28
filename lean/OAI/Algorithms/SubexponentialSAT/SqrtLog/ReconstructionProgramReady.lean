import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramEntry
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgramServices
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramReady

namespace OAI.Algorithms

/-! Static readiness obtained from the physically prepared input tapes.
No arithmetic, program trace, or canonicality hypothesis is hidden here. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.InputReady

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram
open SubexpLiftRing SubexpQuarticRing

/-- Exactly the empty physical ports used by the two native arithmetic banks
and the dense base-word adder. Ports5/10 are populated by the paid entry code. -/
def emptyPorts : List (Fin 320) :=
  [0,1,2,3,4,6,7,8,9,11,12,13,112,113,114,115,116,117,118,119,120,
   128,129,130,131,132,134,135,136,137,138,139,141,142,143,144,
   146,147,148,149,151,152,153,154,155,156,157,158,159,198,199,200]

/-- Definitionally the same store as `NativeState.arithmeticBase`. -/
def base (input : Data) : Fin 256 → List Bool :=
  (Function.update (Entry.prepared input.stacks) 104 (input.stacks 280)) ∘ localPorts

/-- The six unmodified low frame cells are unrestricted input bytes. -/
def lowFrame (input : Data) (i : Fin 6) : List Bool :=
  input.stacks ⟨14+i.val, by omega⟩

theorem nativeReady (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (input : Data) (hc : ∀ i ∈ emptyPorts, input.stacks i = [])
    (hm : input.stacks 194 = M.bits)
    (hw : (input.stacks 202).length = baseWidth p t)
    (hz : input.stacks 203 = cache.zero.val)
    (htable : input.stacks 201 = RingTriple.tableEncoding table)
    (hd : (input.stacks 204).length = d) :
    HornerProgram.Services.NativeReady p t M cache table (base input) := by
  constructor
  · constructor
    · simpa [base, Entry.prepared, localPorts] using hc 120 (by decide)
    · intro i
      fin_cases i <;>
        simp [RingAdapter.ports, RingAdapter.finalNative, RingAdapter.nativeStacks,
          base, Entry.prepared, localPorts]
      all_goals exact hc _ (by decide)
  · simpa [base, Entry.prepared, localPorts] using hm
  · simpa [base, Entry.prepared, localPorts] using hw
  · simpa [base, Entry.prepared, localPorts] using hz
  · simpa [base, Entry.prepared, localPorts] using htable
  · simpa [base, Entry.prepared, localPorts] using hd

theorem polynomialReady (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (input : Data) (hc : ∀ i ∈ emptyPorts, input.stacks i = [])
    (hm : input.stacks 194 = M.bits)
    (hw : (input.stacks 202).length = baseWidth p t)
    (hz : input.stacks 203 = cache.zero.val)
    (htable : input.stacks 201 = RingTriple.tableEncoding table)
    (hd : (input.stacks 204).length = d)
    (hW : (input.stacks 280).length = d*baseWidth p t) :
    DensePolynomialProgram.PairSpec.BaseReady p t M cache table (base input)
      (input.stacks 202) (lowFrame input) := by
  constructor
  · intro i h8 h9
    fin_cases i <;> try contradiction
    all_goals simp [DensePolynomialProgram.RingCall.ports, DensePolynomialProgram.RingCall.port,
      RingScan.serviceState, RingScan.serviceWorkState, RingScan.serviceTapes,
      base, Entry.prepared, localPorts, hm, hz, htable]
    all_goals exact hc _ (by decide)
  · intro i
    fin_cases i <;>
      simp [SubexpConvolutionPair.lowPort, SubexpJetCellProgram.scalarPorts,
        DensePolynomialLoop.ready, DensePolynomialLoop.state, DensePolynomialLoop.stackArray,
        Fin.addCases, Fin.coe_ofNat_eq_mod, base, Entry.prepared, localPorts, lowFrame, hm]
    all_goals exact hc _ (by decide)
  · simpa [base, Entry.prepared, localPorts] using hW
  · exact hw
  · simpa [base, Entry.prepared, localPorts] using hd
  · simpa [base, Entry.prepared, localPorts] using hc 120 (by decide)
  · intro i hlo hhi
    have hi : i = 112 ∨ i = 113 ∨ i = 114 ∨ i = 115 ∨ i = 116 ∨ i = 117 ∨ i = 118 ∨ i = 119 := by
      omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [base, Entry.prepared, localPorts]
    all_goals exact hc _ (by decide)

end SubexponentialSAT.SqrtLog.ReconstructionProgram.InputReady

end OAI.Algorithms
