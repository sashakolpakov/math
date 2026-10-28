import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainMeasuredBound
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawBootBounds

namespace OAI.Algorithms

/-!
# Measured controller bound for the actual ordered-input boot

This is the ordered-input instance of the shared numerical envelope. It uses
the exact boot's startup time and records, and the original ordered input's
bit length. All constants and leaf costs are shared with the Main bound.
-/

namespace SubexponentialSAT.SubexpOrderedRawMeasuredBound

open SubexpComputation SubexpMainProgram SubexpSetupProgram SubexpPackingParameters
  SubexpMainMeasuredBound

variable {cfg : Config} {er n : ℕ} {hr : 32 ≤ workRegs er}
  {F : SubexpOrderedRawPrefix.Formula n}

/-- The measured cost of this boot and its record iterator has the same fixed
envelope as Main. The prefix ceiling is a proof budget, not an executed oracle. -/
theorem measured_bound (boot : SubexpOrderedRawBoot.Run cfg hr F)
    {C A : ℝ} {d : ℕ} (hC : 1 ≤ C) (hA : 0 ≤ A) (good : GoodInput n)
    (hboot : (SubexpOrderedRawBootBounds.totalSteps boot : ℝ) ≤
      runtimeBound C A d (SubexpOrderedRawPrefix.bitLength F) n)
    (hcount : (boot.records.length : ℝ) ≤
      runtimeBound C A d (SubexpOrderedRawPrefix.bitLength F) n) :
    ((SubexpOrderedRawBootBounds.totalSteps boot + 5 + RecordPrograms.budget
      (SubexpMainAssembly.leafCost er (helperSize cfg) n (ell n) (p n)
        (SubexpMainPrefixBudget.limit C A d (SubexpOrderedRawPrefix.bitLength F) n))
      boot.records : ℕ) : ℝ) ≤
      runtimeBound (SubexpMainMeasuredBound.constant cfg er C)
        (SubexpMainMeasuredBound.exponent A) (SubexpMainMeasuredBound.degree cfg d)
        (SubexpOrderedRawPrefix.bitLength F) n := by
  let L := SubexpOrderedRawPrefix.bitLength F
  let K := baseConstant cfg er C
  let E := A+3
  let q := baseDegree cfg d
  let P := runtimeBound K E q L n
  have hC0 : 0 ≤ C := by linarith
  have hk0 : (0 : ℝ) ≤ cfg.k := Nat.cast_nonneg _
  have hh0 : (0 : ℝ) ≤ helperSize cfg := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ workRegs er := Nat.cast_nonneg _
  have hK : 1 ≤ K := by dsimp [K, baseConstant]; push_cast; linarith
  have hE : 0 ≤ E := by dsimp [E]; linarith
  have hCk : C ≤ K := by dsimp [K, baseConstant]; push_cast; linarith
  have h2Ck : 2*C ≤ K := by dsimp [K, baseConstant]; push_cast; linarith
  have hAk : A ≤ E := by dsimp [E]; linarith
  have hdq : d ≤ q := by dsimp [q, baseDegree]; omega
  have hP : 1 ≤ P := one_le_runtimeBound hK hE q L n
  have hbootP : (SubexpOrderedRawBootBounds.totalSteps boot : ℝ) ≤ P :=
    hboot.trans (monotone hC0 hCk hAk hdq L n)
  have hcountP : (boot.records.length : ℝ) ≤ P :=
    hcount.trans (monotone hC0 hCk hAk hdq L n)
  have hprefix (bits : List Bool) :
      (SubexpMainPrefixBudget.limit C A d L n bits : ℝ) ≤ P :=
    (SubexpMainPrefixBudget.limit_le hC hA bits).trans
      (monotone (by positivity) h2Ck hAk hdq L n)
  have hsmall (c t : ℕ) (hc : (c : ℝ) ≤ K) (ht : t ≤ q) :
      ((c*(L+1)^t : ℕ) : ℝ) ≤ P :=
    (polynomial_le c t L n (A := (0 : ℝ)) le_rfl).trans
      (monotone (Nat.cast_nonneg c) hc hE ht L n)
  have hpayload (bits : List Bool) (hb : bits ∈ boot.records) : (bits.length : ℝ) ≤ P := by
    apply (Nat.cast_le.mpr (SubexpOrderedRawBootBounds.record_length boot bits hb)).trans
    apply hsmall (8*cfg.k+5) (2*cfg.k+1)
    · dsimp [K, baseConstant]
      push_cast
      linarith
    · dsimp [q, baseDegree]; omega
  have hwidth : (SubexpLeafContract.wordWidth n (ell n) (p n) : ℝ) ≤ P := by
    apply (Nat.cast_le.mpr
      (word_width_le good (SubexpOrderedRawPrefix.numVariables_le_bitLength F))).trans
    simpa only [one_mul] using hsmall 1 2 (by exact_mod_cast hK) (by dsimp [q, baseDegree]; omega)
  have hhelper : (helperSize cfg : ℝ) ≤ P := by
    have hc : (helperSize cfg : ℝ) ≤ K := by
      dsimp [K, baseConstant]; push_cast; linarith
    simpa only [pow_zero, mul_one] using hsmall (helperSize cfg) 0 hc (Nat.zero_le q)
  have hregs : (workRegs er : ℝ) ≤ P := by
    have hc : (workRegs er : ℝ) ≤ K := by
      dsimp [K, baseConstant]; push_cast; linarith
    simpa only [pow_zero, mul_one] using hsmall (workRegs er) 0 hc (Nat.zero_le q)
  let Q := runtimeBound (50003*K^2) (2*E) (q*2) L n
  have hQeq : Q = 50003*P^2 := by
    dsimp [Q, P]
    rw [runtimeBound_pow, ← runtimeBound_mul_constant]
    norm_num
  have hPQ : P ≤ Q := by rw [hQeq]; nlinarith
  have hQconstant : 1 ≤ 50003*K^2 := by nlinarith
  have hvisits : ∀ bits ∈ boot.records,
      ((6*bits.length + SubexpMainAssembly.leafCost er (helperSize cfg) n (ell n) (p n)
        (SubexpMainPrefixBudget.limit C A d L n) bits + 7 : ℕ) : ℝ) ≤ Q := by
    intro bits hb
    rw [hQeq]
    exact SubexpMainVisitBounds.visit_envelope er (helperSize cfg)
      (SubexpLeafContract.wordWidth n (ell n) (p n))
      (SubexpMainPrefixBudget.limit C A d L n bits) bits hP (hprefix bits)
      (hpayload bits hb) hwidth hhelper hregs
  have total := SubexpMainCostAssembly.measured_envelope
    (SubexpOrderedRawBootBounds.totalSteps boot) boot.records
    (SubexpMainAssembly.leafCost er (helperSize cfg) n (ell n) (p n)
      (SubexpMainPrefixBudget.limit C A d L n)) hQconstant (by positivity : 0 ≤ 2*E)
      (hbootP.trans hPQ) (hcountP.trans hPQ) hvisits
  (convert total using 1; dsimp [constant, exponent, degree, K, E, q, L]; ring_nf)

end SubexponentialSAT.SubexpOrderedRawMeasuredBound

end OAI.Algorithms
