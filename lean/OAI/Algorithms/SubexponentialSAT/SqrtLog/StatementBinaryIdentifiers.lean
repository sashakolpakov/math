import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.RawIdEncoding
import OAI.Algorithms.SubexponentialSAT.SqrtLog.StatementCanonical

namespace OAI.Algorithms

/-!
# The external binary-identifier version of the target

Ordered input may contain repeated literals and repeated clauses.  Identifiers
are literal bit words, not a unary maximum identifier or an implicit promise.
The size parameter is the number of distinct identifiers actually occurring;
input processing is still charged by the full supplied bit length.

This file only specifies and expands the contract.  No transport from the
canonical contract, and no machine satisfying this contract, is asserted here.
-/

namespace SubexponentialSAT.SqrtLog.Statement

open _root_.OAI.Algorithms.SubexponentialSAT.Computation
open Subexp

/-- Uniform measured decision on the unchanged external input syntax. -/
def BinaryIdentifierDecidesWithBound (machine : PrimitiveMachine) (width : ℕ)
    (constant exponentConstant : ℝ) (degree : ℕ) : Prop :=
  ∀ F : RawIdEncoding.Formula, (∀ clause ∈ F, clause.length ≤ width) →
    ∃ (answer : Bool) (time : ℕ),
      machine.OutputsInTime (RawIdEncoding.encode F) answer time ∧
      (answer = true ↔ SAT.Satisfiable (RawIdEncoding.semantics F)) ∧
      (time : ℝ) ≤ runtimeBound constant exponentConstant degree
        (RawIdEncoding.encode F).length (RawIdEncoding.dimension F)

def BinaryIdentifierFeasible (width : ℕ) : Prop :=
  ∃ (machine : PrimitiveMachine) (constant exponentConstant : ℝ) (degree : ℕ),
    0 < constant ∧ 0 < exponentConstant ∧ 0 < degree ∧
      BinaryIdentifierDecidesWithBound machine width constant exponentConstant degree

/-- The external-input target, still a proposition with no existence proof. -/
def BinaryIdentifierMainTheorem : Prop :=
  ∀ width : ℕ, 3 ≤ width → BinaryIdentifierFeasible width

/-- Both encodings have their own fixed machines.  The two formats need not be
decoded by the same machine; within each format the machine is input-independent. -/
def FullMainTheorem : Prop := MainTheorem ∧ BinaryIdentifierMainTheorem

theorem binaryIdentifierMainTheorem_iff_explicit : BinaryIdentifierMainTheorem ↔
    ∀ k : ℕ, 3 ≤ k →
      ∃ (machine : PrimitiveMachine) (C A : ℝ) (d : ℕ),
        0 < C ∧ 0 < A ∧ 0 < d ∧
        ∀ F : RawIdEncoding.Formula, (∀ clause ∈ F, clause.length ≤ k) →
          ∃ (answer : Bool) (time : ℕ),
            (∃ c : machine.Cfg,
              RunsIn machine.step time (machine.init (RawIdEncoding.encode F)) c ∧
              c.state = Sum.inl answer) ∧
            (answer = true ↔ SAT.Satisfiable (RawIdEncoding.semantics F)) ∧
            (time : ℝ) ≤ C * (((RawIdEncoding.encode F).length : ℝ) + 1) ^ d *
              (2 : ℝ) ^ (A * runtimeScale (RawIdEncoding.dimension F)) := by
  rfl

theorem binaryIdentifierFeasible_width_antitone {width width' : ℕ}
    (hw : width ≤ width') (h : BinaryIdentifierFeasible width') :
    BinaryIdentifierFeasible width := by
  obtain ⟨machine, C, A, d, hC, hA, hd, hdec⟩ := h
  refine ⟨machine, C, A, d, hC, hA, hd, ?_⟩
  intro F hF
  exact hdec F (fun clause hc => (hF clause hc).trans hw)

end SubexponentialSAT.SqrtLog.Statement

end OAI.Algorithms
