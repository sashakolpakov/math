import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionController
import OAI.Algorithms.SubexponentialSAT.SubexpRawIDRuntime

namespace OAI.Algorithms

/-!
# Concrete cutoff completion and binary-identifier transport

These wrappers reuse the audited finite cutoff scanner and physical identifier
renamer. The remaining premise is a family of actual large-input controller
certificates. No stronger solver or large-input certificate is asserted here.
The bounds below count primitive transitions and preserve every input meaning.
-/

namespace SubexponentialSAT.SqrtLog.Execution

open SubexpMainProgram

variable {er es : ℕ}

/-- A named, explicit unproved obligation for the new implementations. -/
def LargeCanonicalContract (phases : Phases er es) (leaf : MainCmd er es)
    (width cutoff : ℕ) (time : ℕ → ℕ → ℕ) : Prop :=
  ∀ n (F : SAT.CNF (Fin n)), SAT.WidthAtMost width F → cutoff ≤ n →
    ∃ (b : Budget) (_cert : CanonicalCertificate phases leaf F b),
      b.total ≤ time n (Encoding.formulaBitLength F)

/-- The ordered-list contract is needed separately: canonical finite-set
correctness alone does not justify duplicate or reordered input records. -/
def LargeOrderedContract (phases : Phases er es) (leaf : MainCmd er es)
    (width cutoff : ℕ) (time : ℕ → ℕ → ℕ) : Prop :=
  ∀ n (F : SubexpOrderedRawPrefix.Formula n),
    ExecSunflowerSearch.RawWidthAtMost width F → cutoff ≤ n →
    ∃ (b : Budget) (_cert : OrderedCertificate phases leaf F b),
      b.total ≤ time n (SubexpOrderedRawPrefix.bitLength F)

noncomputable def completedCanonicalMachine (phases : Phases er es)
    (leaf : MainCmd er es) (cutoff : ℕ) : Computation.PrimitiveMachine :=
  BitProgram.primitive (FinitePrefixProgram.completed (program phases leaf) cutoff)

noncomputable def completedOrderedMachine (phases : Phases er es)
    (leaf : MainCmd er es) (cutoff : ℕ) : Computation.PrimitiveMachine :=
  BitProgram.primitive (SubexpOrderedRawCompletion.completed (program phases leaf) cutoff)

theorem completedCanonical_outputs (phases : Phases er es) (leaf : MainCmd er es)
    (width cutoff : ℕ) (time : ℕ → ℕ → ℕ)
    (large : LargeCanonicalContract phases leaf width cutoff time)
    (n : ℕ) (F : SAT.CNF (Fin n)) (hF : SAT.WidthAtMost width F) :
    ∃ answer, (completedCanonicalMachine phases leaf cutoff).OutputsInTime
      (Encoding.encodeCNF F) answer
      (BitProgram.primitiveOverhead
        (FinitePrefixProgram.completed (program phases leaf) cutoff) *
        (6 * cutoff + 3 * Encoding.formulaBitLength F +
          time n (Encoding.formulaBitLength F) + 12)) ∧
      (answer = true ↔ SAT.Satisfiable F) := by
  apply FinitePrefixProgram.primitive_completes_eventual_dirty
    (program phases leaf) cutoff width time ?_ n F hF
  intro m G hG hm
  obtain ⟨b, cert, hb⟩ := large m G hG hm
  obtain ⟨t, final, hr, hh, ho, hc, ht⟩ := cert.run.runs
  exact ⟨final, cert.run.records.any cert.run.test,
    hr.mono ((ht.trans cert.bound).trans hb), hh, ho, hc⟩

/-- Source-level completed run, used both for primitive output and the
identifier transport. The finite cutoff scanner is already implemented. -/
theorem completedOrdered_runs (phases : Phases er es) (leaf : MainCmd er es)
    (width cutoff : ℕ) (time : ℕ → ℕ → ℕ)
    (large : LargeOrderedContract phases leaf width cutoff time)
    (n : ℕ) (F : SubexpOrderedRawPrefix.Formula n)
    (hF : ExecSunflowerSearch.RawWidthAtMost width F) :
    ∃ final answer,
      BitProgram.RunsIn
        (SubexpOrderedRawCompletion.completed (program phases leaf) cutoff)
        (6 * cutoff + 3 * SubexpOrderedRawPrefix.bitLength F +
          time n (SubexpOrderedRawPrefix.bitLength F) + 12)
        (BitProgram.initial
          (SubexpOrderedRawCompletion.completed (program phases leaf) cutoff)
          (SubexpOrderedRawPrefix.encode F)) final ∧
      final.pc = none ∧
      (final.stacks (program phases leaf).outputStack).head? = some answer ∧
      (answer = true ↔ SAT.Satisfiable (ExecCNF.formulaSet F)) := by
  apply SubexpOrderedRawCompletion.completes_eventual_dirty
    (program phases leaf) cutoff width time ?_ n F hF
  intro m G hG hm
  obtain ⟨b, cert, hb⟩ := large m G hG hm
  obtain ⟨final, hr, hh, ho⟩ := cert.run.runs
  exact ⟨final, cert.run.records.any cert.run.test,
    hr.mono (cert.bound.trans hb), hh, ho, cert.run.correct⟩

theorem completedOrdered_outputs (phases : Phases er es) (leaf : MainCmd er es)
    (width cutoff : ℕ) (time : ℕ → ℕ → ℕ)
    (large : LargeOrderedContract phases leaf width cutoff time)
    (n : ℕ) (F : SubexpOrderedRawPrefix.Formula n)
    (hF : ExecSunflowerSearch.RawWidthAtMost width F) :
    ∃ answer, (completedOrderedMachine phases leaf cutoff).OutputsInTime
      (SubexpOrderedRawPrefix.encode F) answer
      (BitProgram.primitiveOverhead
        (SubexpOrderedRawCompletion.completed (program phases leaf) cutoff) *
        (6 * cutoff + 3 * SubexpOrderedRawPrefix.bitLength F +
          time n (SubexpOrderedRawPrefix.bitLength F) + 12)) ∧
      (answer = true ↔ SAT.Satisfiable (ExecCNF.formulaSet F)) := by
  obtain ⟨final, answer, hr, hh, ho, hs⟩ :=
    completedOrdered_runs phases leaf width cutoff time large n F hF
  exact ⟨answer, BitProgram.primitive_outputs_of_halted _ hr hh ho, hs⟩

/-- The renamer, cutoff scanner, and supplied finite controller form one
finite machine. Its definition depends on width-fixed code and cutoff only. -/
noncomputable def rawIdentifierMachine (phases : Phases er es)
    (leaf : MainCmd er es) (cutoff : ℕ) : Computation.PrimitiveMachine :=
  BitProgram.primitive (SubexpRawIDRuntime.program phases leaf cutoff)

/-- Fully charged raw-identifier output. The ordered payload size is retained
explicitly; the audited renamer separately bounds it by 17*(inputBits+1)^3.
No dimension change occurs between the renamed input and its controller. -/
theorem rawIdentifier_outputs (phases : Phases er es) (leaf : MainCmd er es)
    (width cutoff : ℕ) (time : ℕ → ℕ → ℕ)
    (large : LargeOrderedContract phases leaf width cutoff time)
    (F : Subexp.RawIdEncoding.Formula) (hF : ∀ C ∈ F, C.length ≤ width) :
    let G := Subexp.RawIdRenaming.physicalRows F
    let L := (Subexp.RawIdEncoding.encode F).length
    ∃ answer, (rawIdentifierMachine phases leaf cutoff).OutputsInTime
      (Subexp.RawIdEncoding.encode F) answer
      (BitProgram.primitiveOverhead (SubexpRawIDRuntime.program phases leaf cutoff) *
        (41000 * (L + 1)^6 + 6 * cutoff +
          3 * SubexpOrderedRawPrefix.bitLength G +
          time (Subexp.RawIdEncoding.dimension F) (SubexpOrderedRawPrefix.bitLength G) + 12)) ∧
      (answer = true ↔ SAT.Satisfiable (Subexp.RawIdEncoding.semantics F)) := by
  dsimp only
  let G := Subexp.RawIdRenaming.physicalRows F
  have hG : ExecSunflowerSearch.RawWidthAtMost width G :=
    Subexp.RawIdRenaming.physical_rawWidth F width hF
  obtain ⟨final, answer, hr, hh, ho, hs⟩ := completedOrdered_runs phases leaf
    width cutoff time large (Subexp.RawIdEncoding.dimension F) G hG
  obtain ⟨pre, hpre, hpreBound⟩ := SubexpRawIDRuntime.transport_execution er es F
  have hout := SubexpOrderedRawCompletion.transported_output
    (program phases leaf) cutoff (SubexpRawIDRuntime.transport er es)
    (Subexp.RawIdEncoding.encode F) G pre
    (6 * cutoff + 3 * SubexpOrderedRawPrefix.bitLength G +
      time (Subexp.RawIdEncoding.dimension F) (SubexpOrderedRawPrefix.bitLength G) + 12)
    hpre final answer hr hh ho
  refine ⟨answer, Computation.PrimitiveMachine.outputsInTime_mono hout ?_, hs.trans
    (Subexp.RawIdRenaming.physical_satisfiable F)⟩
  apply Nat.mul_le_mul_left
  dsimp only [G] at *
  omega

end SubexponentialSAT.SqrtLog.Execution

end OAI.Algorithms
