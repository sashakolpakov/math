import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainController
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawRuntime
import OAI.Algorithms.SubexponentialSAT.SqrtLog.StatementCanonical

namespace OAI.Algorithms

/-!
# Reusable measured controller for the stronger algorithm

The program is the audited fixed controller. New setup, sparsification and
leaf implementations must supply actual execution certificates below. This
module neither implements those missing phases nor asserts that their
certificates exist. Its conclusions use primitive tape transitions, with the
fixed compiler overhead included. No semantic callback is an instruction.
-/

namespace SubexponentialSAT.SqrtLog.Execution

open SubexpMainProgram

/-- Six independent bounds for one concrete run. All leaves, including those
after an early successful answer, may be charged by this upper bound. -/
structure Budget where
  prefixSteps : ℕ
  setupSteps : ℕ
  sparsifySteps : ℕ
  leaves : ℕ
  payloadBits : ℕ
  leafSteps : ℕ

def Budget.total (b : Budget) : ℕ :=
  b.prefixSteps + b.setupSteps + b.sparsifySteps + 5 +
    b.leaves * (6 * b.payloadBits + b.leafSteps + 7)

variable {er es : ℕ}

/-- This is an actual finite program, chosen before any input is supplied. -/
abbrev program (phases : Phases er es) (leaf : MainCmd er es) :=
  SubexpMainController.program phases leaf

noncomputable def machine (phases : Phases er es) (leaf : MainCmd er es) :
    Computation.PrimitiveMachine := BitProgram.primitive (program phases leaf)

noncomputable def overhead (phases : Phases er es) (leaf : MainCmd er es) : ℕ :=
  BitProgram.primitiveOverhead (program phases leaf)

theorem overhead_pos (phases : Phases er es) (leaf : MainCmd er es) :
    0 < overhead phases leaf := BitProgram.primitiveOverhead_pos _

/-- The inherited run includes the physical frontend, setup and splitter
traces, a traced leaf callback contract, framed output leaves, and SAT
coverage. The six extra fields only bound that already actual execution. -/
structure CanonicalCertificate (phases : Phases er es) (leaf : MainCmd er es)
    {n : ℕ} (F : SAT.CNF (Fin n)) (b : Budget) where
  run : SubexpMainController.Execution phases leaf F
  prefixBound : run.prefixSteps ≤ b.prefixSteps
  setupBound : run.boot.setupSteps ≤ b.setupSteps
  sparsifyBound : run.boot.sparsifySteps ≤ b.sparsifySteps
  leafCountBound : run.records.length ≤ b.leaves
  payloadBound : ∀ bits ∈ run.records, bits.length ≤ b.payloadBits
  leafBound : ∀ bits ∈ run.records, run.cost bits ≤ b.leafSteps

theorem CanonicalCertificate.bound {phases : Phases er es} {leaf : MainCmd er es}
    {n : ℕ} {F : SAT.CNF (Fin n)} {b : Budget}
    (cert : CanonicalCertificate phases leaf F b) : cert.run.bound ≤ b.total := by
  exact cert.run.bound_le b.prefixSteps b.setupSteps b.sparsifySteps b.leaves
    b.payloadBits b.leafSteps cert.prefixBound cert.setupBound cert.sparsifyBound
    cert.leafCountBound cert.payloadBound cert.leafBound

/-- The returned primitive-time bound includes the actual compiler overhead.
No cleaned final work-stack state is needed, only the proved output head. -/
theorem CanonicalCertificate.outputs {phases : Phases er es} {leaf : MainCmd er es}
    {n : ℕ} {F : SAT.CNF (Fin n)} {b : Budget}
    (cert : CanonicalCertificate phases leaf F b) :
    ∃ answer, (machine phases leaf).OutputsInTime (Encoding.encodeCNF F) answer
      (overhead phases leaf * b.total) ∧
      (answer = true ↔ SAT.Satisfiable F) := by
  obtain ⟨t, final, hr, hh, ho, hc, ht⟩ := cert.run.runs
  exact ⟨cert.run.records.any cert.run.test,
    BitProgram.primitive_outputs_of_halted _ (hr.mono (ht.trans cert.bound)) hh ho, hc⟩

/-- An ordered input uses the same finite controller, preserving duplicate
clauses and literal order until the real normalization phase executes. -/
structure OrderedCertificate (phases : Phases er es) (leaf : MainCmd er es)
    {n : ℕ} (F : SubexpOrderedRawPrefix.Formula n) (b : Budget) where
  run : SubexpOrderedRawRuntime.Execution phases leaf F
  prefixBound : run.prefixSteps ≤ b.prefixSteps
  setupBound : run.boot.setupSteps ≤ b.setupSteps
  sparsifyBound : run.boot.sparsifySteps ≤ b.sparsifySteps
  leafCountBound : run.records.length ≤ b.leaves
  payloadBound : ∀ bits ∈ run.records, bits.length ≤ b.payloadBits
  leafBound : ∀ bits ∈ run.records, run.cost bits ≤ b.leafSteps

theorem OrderedCertificate.bound {phases : Phases er es} {leaf : MainCmd er es}
    {n : ℕ} {F : SubexpOrderedRawPrefix.Formula n} {b : Budget}
    (cert : OrderedCertificate phases leaf F b) : cert.run.bound ≤ b.total := by
  exact cert.run.bound_le b.prefixSteps b.setupSteps b.sparsifySteps b.leaves
    b.payloadBits b.leafSteps cert.prefixBound cert.setupBound cert.sparsifyBound
    cert.leafCountBound cert.payloadBound cert.leafBound

theorem OrderedCertificate.outputs {phases : Phases er es} {leaf : MainCmd er es}
    {n : ℕ} {F : SubexpOrderedRawPrefix.Formula n} {b : Budget}
    (cert : OrderedCertificate phases leaf F b) :
    ∃ answer, (machine phases leaf).OutputsInTime (SubexpOrderedRawPrefix.encode F)
      answer (overhead phases leaf * b.total) ∧
      (answer = true ↔ SAT.Satisfiable (ExecCNF.formulaSet F)) := by
  obtain ⟨final, hr, hh, ho⟩ := cert.run.runs
  exact ⟨cert.run.records.any cert.run.test,
    BitProgram.primitive_outputs_of_halted _ (hr.mono cert.bound) hh ho,
    cert.run.correct⟩

/-- Conditional rate transfer. The all-input certificate family and its new
square-root-log budget are explicit assumptions, not obtained in this file. -/
theorem canonical_decides_of_certificates (phases : Phases er es)
    (leaf : MainCmd er es) (width : ℕ) (C A : ℝ) (d : ℕ)
    (certificates : ∀ n (F : SAT.CNF (Fin n)), SAT.WidthAtMost width F →
      ∃ (b : Budget) (_cert : CanonicalCertificate phases leaf F b),
        (b.total : ℝ) ≤ Statement.runtimeBound C A d (Encoding.formulaBitLength F) n) :
    Statement.DecidesWithBound (machine phases leaf) width
      ((overhead phases leaf : ℝ) * C) A d := by
  intro n F hF
  obtain ⟨b, cert, hb⟩ := certificates n F hF
  obtain ⟨answer, ht, hs⟩ := cert.outputs
  refine ⟨answer, overhead phases leaf * b.total, ht, hs, ?_⟩
  rw [Nat.cast_mul, Statement.runtimeBound_mul_constant]
  exact mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)

/-- This produces the exact stronger primitive-machine statement only when
all actual phase certificates and their rate bounds have been supplied. -/
theorem canonical_feasible_of_certificates (phases : Phases er es)
    (leaf : MainCmd er es) (width : ℕ) (C A : ℝ) (d : ℕ)
    (hC : 0 < C) (hA : 0 < A) (hd : 0 < d)
    (certificates : ∀ n (F : SAT.CNF (Fin n)), SAT.WidthAtMost width F →
      ∃ (b : Budget) (_cert : CanonicalCertificate phases leaf F b),
        (b.total : ℝ) ≤ Statement.runtimeBound C A d (Encoding.formulaBitLength F) n) :
    Statement.Feasible width := by
  exact ⟨machine phases leaf, (overhead phases leaf : ℝ) * C, A, d,
    mul_pos (Nat.cast_pos.mpr (overhead_pos phases leaf)) hC, hA, hd,
    canonical_decides_of_certificates phases leaf width C A d certificates⟩

end SubexponentialSAT.SqrtLog.Execution

end OAI.Algorithms
