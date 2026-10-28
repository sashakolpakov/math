import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainRawIDTransport
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawCompletion

namespace OAI.Algorithms

/-! Actual binary-identifier transport precedes the ordered-input cutoff.
The only remaining solver hypothesis is correctness and time for the fixed
ordered solver. The remapper, byte-size bound, and SAT equivalence are the
concrete proved implementations, not callback assumptions. -/

namespace SubexponentialSAT.SubexpRawIDRuntime

open BitProgram StructuredCalls SubexpMainProgram
open Subexp
open SubexpOrderedRawCompletion (completed ProgramDecidesWithBound)

private abbrev castCommand {r r' s : ℕ} (h : r = r') (c : Cmd r s) : Cmd r' s := h ▸ c

private theorem castCommand_eval {r r' s : ℕ} (h : r = r') (c : Cmd r s)
    (n : ℕ) (port : Fin s) (input output : List Bool)
    (he : Eval c n (StructuredProgram.ioState port input)
      (StructuredProgram.ioState port output)) :
    Eval (castCommand h c) n (StructuredProgram.ioState port input)
      (StructuredProgram.ioState port output) := by
  subst r'
  exact he

private theorem registerCount (er : ℕ) : totalRegs (er + 3) = 3 + totalRegs er := by
  dsimp [totalRegs, workRegs]
  omega

abbrev transport (er es : ℕ) : Cmd (3 + totalRegs er) (totalStacks es) :=
  castCommand (registerCount er) (SubexpMainRawIDTransport.command (er + 3) es)

theorem transport_execution (er es : ℕ) (F : RawIdEncoding.Formula) :
    ∃ t, Eval (transport er es) t
      (StructuredProgram.ioState (persistent es 0) (RawIdEncoding.encode F))
      (StructuredProgram.ioState (persistent es 0)
        (SubexpOrderedRawPrefix.encode (RawIdRenaming.physicalRows F))) ∧
      t + 1 ≤ 41000 * ((RawIdEncoding.encode F).length + 1)^6 := by
  obtain ⟨t, ht, hb⟩ := SubexpMainRawIDTransport.ordered_execution (er + 3) es F
  exact ⟨t, castCommand_eval (registerCount er) _ t (persistent es 0) _ _ ht, hb⟩

noncomputable def program {er es : ℕ} (p : Phases er es) (leaf : MainCmd er es) (N : ℕ) :=
  SubexpOrderedRawCompletion.transportProgram (SubexpMainController.program p leaf) N
    (transport er es)

def DecidesWithBound (machine : Computation.PrimitiveMachine) (width : ℕ)
    (constant exponentConstant : ℝ) (degree : ℕ) : Prop :=
  ∀ F : RawIdEncoding.Formula, (∀ C ∈ F, C.length ≤ width) →
    ∃ answer time, machine.OutputsInTime (RawIdEncoding.encode F) answer time ∧
      (answer = true ↔ SAT.Satisfiable (RawIdEncoding.semantics F)) ∧
      (time : ℝ) ≤ SubexpComputation.runtimeBound constant exponentConstant degree
        (RawIdEncoding.encode F).length (RawIdEncoding.dimension F)

def Feasible (width : ℕ) : Prop :=
  ∃ (machine : Computation.PrimitiveMachine) (constant exponentConstant : ℝ) (degree : ℕ),
    0 < constant ∧ 0 < exponentConstant ∧ 0 < degree ∧
      DecidesWithBound machine width constant exponentConstant degree

/-- All input handling is now actual code. The source solver contract refers
to the fixed completed ordered machine, including its real small-input arm.
The exponent and polynomial slowdowns below are fixed, independent of F. -/
theorem of_completed {er es : ℕ} (p : Phases er es) (leaf : MainCmd er es)
    (N width : ℕ) (constant exponentConstant : ℝ) (degree : ℕ)
    (hc : 1 ≤ constant) (ha : 0 ≤ exponentConstant) (hd : 0 < degree)
    (hcore : ProgramDecidesWithBound (completed (SubexpMainController.program p leaf) N)
      width constant exponentConstant degree) :
    DecidesWithBound (primitive (program p leaf N)) width
      (((primitiveOverhead (program p leaf N) * 41001 : ℕ) : ℝ) *
        (2 * (constant * (17 : ℝ)^degree))^6)
      (6 * exponentConstant) (3 * degree * 6) := by
  intro F hF
  let G := RawIdRenaming.physicalRows F
  let L := (RawIdEncoding.encode F).length
  have hG : ExecSunflowerSearch.RawWidthAtMost width G :=
    RawIdRenaming.physical_rawWidth F width hF
  obtain ⟨answer, time, final, hrun, hhalt, hout, hsat, htime⟩ :=
    hcore (RawIdEncoding.dimension F) G hG
  obtain ⟨pre, hpre, hprebound⟩ := transport_execution er es F
  have hexec := SubexpOrderedRawCompletion.transported_output
    (SubexpMainController.program p leaf) N (transport er es) (RawIdEncoding.encode F)
    G pre time hpre final answer hrun hhalt hout
  refine ⟨answer, primitiveOverhead (program p leaf N) * (pre + time + 1), hexec,
    hsat.trans (RawIdRenaming.physical_satisfiable F), ?_⟩
  have hsize : (SubexpOrderedRawPrefix.bitLength G : ℝ) + 1 ≤
      17 * ((L : ℝ) + 1)^3 := by
    exact_mod_cast SubexpMainRawIDTransport.ordered_size F
  have hcommon : (time : ℝ) ≤ SubexpComputation.runtimeBound
      (constant * (17 : ℝ)^degree) exponentConstant (3 * degree) L
      (RawIdEncoding.dimension F) :=
    htime.trans (SubexpComputation.polynomial_input_overhead_le (by linarith) ha
      (by norm_num) degree 3 L (SubexpOrderedRawPrefix.bitLength G)
      (RawIdEncoding.dimension F) (RawIdEncoding.dimension F) hsize le_rfl)
  have hconstant : 1 ≤ constant * (17 : ℝ)^degree :=
    one_le_mul_of_one_le_of_one_le hc (one_le_pow₀ (by norm_num))
  have hdegree : 0 < 3 * degree := Nat.mul_pos (by decide) hd
  have hpow : (L + 1)^6 ≤ (time + L + 1)^6 :=
    Nat.pow_le_pow_left (by omega) 6
  have ht : time ≤ (time + L + 1)^6 :=
    (show time ≤ time + L + 1 by omega).trans (Nat.le_self_pow (by decide) _)
  have hpre' : pre + 1 ≤ 41000 * (time + L + 1)^6 :=
    hprebound.trans (Nat.mul_le_mul_left 41000 hpow)
  have htotal : primitiveOverhead (program p leaf N) * (pre + time + 1) ≤
      (primitiveOverhead (program p leaf N) * 41001) * (time + L + 1)^6 := by
    calc
      _ ≤ primitiveOverhead (program p leaf N) * (41001 * (time + L + 1)^6) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  simpa only [Nat.cast_ofNat] using
    SubexpComputation.nat_polynomial_overhead_le hconstant ha hdegree
      L (RawIdEncoding.dimension F) 6 (primitiveOverhead (program p leaf N) * 41001)
      time (primitiveOverhead (program p leaf N) * (pre + time + 1)) hcommon htotal

/-- Conditional final transport theorem. The remaining premise is the actual
uniform large-input Main execution; raw-ID preprocessing, the ordered small
fallback, and all their costs are implemented by the fixed resulting machine.
The cutoff and all constants precede every external formula. -/
theorem feasible_of_eventual_executions {er es : ℕ}
    (p : Phases er es) (leaf : MainCmd er es) (width : ℕ)
    {constant exponentConstant : ℝ} {degree : ℕ}
    (hc : 1 ≤ constant) (ha : 0 < exponentConstant) (hd : 0 < degree)
    (large : ∀ᶠ n in Filter.atTop, ∀ G : SubexpOrderedRawPrefix.Formula n,
      ExecSunflowerSearch.RawWidthAtMost width G →
        ∃ run : SubexpOrderedRawRuntime.Execution p leaf G,
          (run.bound : ℝ) ≤ SubexpComputation.runtimeBound constant exponentConstant degree
            (SubexpOrderedRawPrefix.bitLength G) n) : Feasible width := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp large
  have habove : SubexpOrderedRawCompletion.DecidesAbove (SubexpMainController.program p leaf)
      N width constant exponentConstant degree := by
    intro n G hG hn
    obtain ⟨run, hb⟩ := hN n hn G hG
    obtain ⟨final, ht, hh, ho⟩ := run.runs
    exact ⟨run.records.any run.test, run.bound, final, ht, hh, ho, run.correct, hb⟩
  let C : ℝ := ((6 * N + 16 : ℕ) : ℝ) * (2 * constant)
  have hC : 1 ≤ C := by
    have hN' : (1 : ℝ) ≤ ((6 * N + 16 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 6 * N + 16)
    exact one_le_mul_of_one_le_of_one_le hN' (by linarith)
  have hcore : ProgramDecidesWithBound (completed (SubexpMainController.program p leaf) N)
      width C exponentConstant degree :=
    SubexpOrderedRawCompletion.completed_decidesWithBound
      (SubexpMainController.program p leaf) N width hc ha.le hd habove
  have hraw := of_completed p leaf N width C exponentConstant degree hC ha.le hd hcore
  refine ⟨primitive (program p leaf N), _, 6 * exponentConstant, 3 * degree * 6,
    ?_, by positivity, by omega, hraw⟩
  have hoverNat : 0 < primitiveOverhead (program p leaf N) := primitiveOverhead_pos _
  have hover : (0 : ℝ) < primitiveOverhead (program p leaf N) := Nat.cast_pos.mpr hoverNat
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  positivity

end SubexponentialSAT.SubexpRawIDRuntime

end OAI.Algorithms
