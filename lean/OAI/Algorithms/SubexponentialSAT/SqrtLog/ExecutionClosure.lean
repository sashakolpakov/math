import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionCompletion
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionCanonical
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionRuntime
import OAI.Algorithms.SubexponentialSAT.SqrtLog.StatementBinaryIdentifiers

namespace OAI.Algorithms

/-! Closing the real cutoff and identifier wrappers.  The one remaining
hypothesis is explicitly a family of actual large-input execution certificates;
this module does not assert that the leaf implementation supplies it. -/
namespace SubexponentialSAT.SqrtLog.Execution

open SubexpMainProgram Statement Filter

variable {er es : ℕ}

theorem canonical_feasible_of_large_ordered
    (phases : Phases er es) (leaf : MainCmd er es) (width N : ℕ)
    (C A : ℝ) (d : ℕ) (hC : 1 ≤ C) (hA : 0 < A) (hd : 0 < d)
    (large : LargeOrderedContract phases leaf width N
      (fun n L => Nat.ceil (runtimeBound C A d L n))) : Feasible width := by
  have hCp : 0 < C := lt_of_lt_of_le (by norm_num) hC
  let O := BitProgram.primitiveOverhead
    (SubexpOrderedRawCompletion.completed (program phases leaf) N)
  have hO : (0 : ℝ) < O := Nat.cast_pos.mpr (BitProgram.primitiveOverhead_pos _)
  refine ⟨completedOrderedMachine phases leaf N,
    (O : ℝ)*(((6*N+17 : ℕ) : ℝ)*C),A,d,by positivity,hA,hd,?_⟩
  intro n F hF
  let G := ExecQuantitativeSparsify.formulaList F
  have hG := ExecQuantitativeSparsify.formulaList_width F width hF
  obtain ⟨answer,hrun,hcorrect⟩ := completedOrdered_outputs phases leaf width N
    (fun n L => Nat.ceil (runtimeBound C A d L n)) large n G hG
  have hbits : SubexpOrderedRawPrefix.bitLength G = Encoding.formulaBitLength F :=
    ordered_canonical_bits F
  rw [ordered_canonical_encoding,hbits] at hrun
  have hc : answer = true ↔ SAT.Satisfiable F := by
    simpa only [G,ExecQuantitativeSparsify.formulaList_set] using hcorrect
  refine ⟨answer,O*(6*N+3*Encoding.formulaBitLength F+
    Nat.ceil (runtimeBound C A d (Encoding.formulaBitLength F) n)+12),hrun,hc,?_⟩
  rw [Nat.cast_mul,runtimeBound_mul_constant]
  exact mul_le_mul_of_nonneg_left (cutoff_source_bound hC hA.le hd N _ n)
    (Nat.cast_nonneg O)

theorem binary_feasible_of_large_ordered
    (phases : Phases er es) (leaf : MainCmd er es) (width N : ℕ)
    (C A : ℝ) (d : ℕ) (hC : 1 ≤ C) (hA : 0 < A) (hd : 0 < d)
    (large : LargeOrderedContract phases leaf width N
      (fun n L => Nat.ceil (runtimeBound C A d L n))) :
    BinaryIdentifierFeasible width := by
  have hCp : 0 < C := lt_of_lt_of_le (by norm_num) hC
  let O := BitProgram.primitiveOverhead (SubexpRawIDRuntime.program phases leaf N)
  let C0 : ℝ := ((6*N+17 : ℕ) : ℝ)*C
  let C1 : ℝ := C0*17^d
  have hO : (0 : ℝ) < O := Nat.cast_pos.mpr (BitProgram.primitiveOverhead_pos _)
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  have hC1 : 0 < C1 := by dsimp [C1]; positivity
  refine ⟨rawIdentifierMachine phases leaf N,(O : ℝ)*(41000+C1),A,6+3*d,
    by positivity,hA,by omega,?_⟩
  intro F hF
  let G := Subexp.RawIdRenaming.physicalRows F
  let L := (Subexp.RawIdEncoding.encode F).length
  let n := Subexp.RawIdEncoding.dimension F
  obtain ⟨answer,hrun,hcorrect⟩ := rawIdentifier_outputs phases leaf width N
    (fun n L => Nat.ceil (runtimeBound C A d L n)) large F hF
  have hsize : (SubexpOrderedRawPrefix.bitLength G : ℝ)+1 ≤
      17*((L : ℝ)+1)^3 := by
    exact_mod_cast SubexpMainRawIDTransport.ordered_size F
  have hcut := cutoff_source_bound hC hA.le hd N
    (SubexpOrderedRawPrefix.bitLength G) n
  have hsub : runtimeBound C0 A d (SubexpOrderedRawPrefix.bitLength G) n ≤
      runtimeBound C1 A (3*d) L n :=
    runtimeBound_input_substitution hC0.le hA.le (by norm_num) d 3 L _ n n hsize le_rfl
  have hdeg := runtimeBound_mono_degree (A := A) hC1.le
    (by omega : 3*d ≤ 6+3*d) L n
  have htail : ((6*N+3*SubexpOrderedRawPrefix.bitLength G+
      Nat.ceil (runtimeBound C A d (SubexpOrderedRawPrefix.bitLength G) n)+12 : ℕ) : ℝ) ≤
      runtimeBound C1 A (6+3*d) L n := (hcut.trans hsub).trans hdeg
  have hbase : (1 : ℝ) ≤ (L : ℝ)+1 := by
    have := Nat.cast_nonneg (α := ℝ) L
    linarith
  have hp : ((L : ℝ)+1)^6 ≤ ((L : ℝ)+1)^(6+3*d) :=
    pow_le_pow_right₀ hbase (by omega)
  have hexp : (1 : ℝ) ≤ (2 : ℝ)^(A*runtimeScale n) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg hA.le (runtimeScale_nonneg n))
  have hpre : 41000*((L : ℝ)+1)^6 ≤ runtimeBound 41000 A (6+3*d) L n := by
    calc
      _ ≤ 41000*((L : ℝ)+1)^(6+3*d) := by nlinarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hexp
  have hsource : ((41000*(L+1)^6+6*N+3*SubexpOrderedRawPrefix.bitLength G+
      Nat.ceil (runtimeBound C A d (SubexpOrderedRawPrefix.bitLength G) n)+12 : ℕ) : ℝ) ≤
      runtimeBound (41000+C1) A (6+3*d) L n := by
    push_cast at htail ⊢
    unfold runtimeBound at htail hpre ⊢
    nlinarith
  refine ⟨answer,O*(41000*(L+1)^6+6*N+3*SubexpOrderedRawPrefix.bitLength G+
    Nat.ceil (runtimeBound C A d (SubexpOrderedRawPrefix.bitLength G) n)+12),
    hrun,hcorrect,?_⟩
  rw [Nat.cast_mul,runtimeBound_mul_constant]
  exact mul_le_mul_of_nonneg_left hsource (Nat.cast_nonneg O)

/-- All constants and the completed programs are chosen before the input.
In particular, the exceptional finite range uses real exhaustive code rather
than an absorption claim about a possibly unimplemented small-input path. -/
theorem feasible_pair_of_eventual_certificates
    (phases : Phases er es) (leaf : MainCmd er es) (width : ℕ)
    (C A : ℝ) (d : ℕ) (hC : 1 ≤ C) (hA : 0 < A) (hd : 0 < d)
    (large : ∀ᶠ n : ℕ in atTop, ∀ F : SubexpOrderedRawPrefix.Formula n,
      ExecSunflowerSearch.RawWidthAtMost width F →
      ∃ (b : Budget) (_cert : OrderedCertificate phases leaf F b),
        (b.total : ℝ) ≤ runtimeBound C A d (SubexpOrderedRawPrefix.bitLength F) n) :
    Feasible width ∧ BinaryIdentifierFeasible width := by
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp large
  have hlarge : LargeOrderedContract phases leaf width N
      (fun n L => Nat.ceil (runtimeBound C A d L n)) := by
    intro n F hF hn
    obtain ⟨b,cert,hb⟩ := hN n hn F hF
    refine ⟨b,cert,?_⟩
    have hceil := hb.trans (Nat.le_ceil (runtimeBound C A d
      (SubexpOrderedRawPrefix.bitLength F) n))
    exact_mod_cast hceil
  exact ⟨canonical_feasible_of_large_ordered phases leaf width N C A d hC hA hd hlarge,
    binary_feasible_of_large_ordered phases leaf width N C A d hC hA hd hlarge⟩

end SubexponentialSAT.SqrtLog.Execution

end OAI.Algorithms
