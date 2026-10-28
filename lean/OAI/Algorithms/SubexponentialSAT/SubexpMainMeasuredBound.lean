import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainPrefixBudget
import OAI.Algorithms.SubexponentialSAT.SubexpMainInitialState

namespace OAI.Algorithms

/-! Close the measured controller budget once the actual backend prefix
has a uniform bound. Parsing, guards, decoding and cleanup are included. -/

namespace SubexponentialSAT.SubexpMainMeasuredBound

open SubexpComputation SubexpMainProgram SubexpSetupProgram SubexpPackingParameters

theorem monotone {C C' A A' : ℝ} {d d' : ℕ}
    (hC : 0 ≤ C) (hc : C ≤ C') (ha : A ≤ A') (hd : d ≤ d') (L n : ℕ) :
    runtimeBound C A d L n ≤ runtimeBound C' A' d' L n := by
  have hb : (1 : ℝ) ≤ (L : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) L; linarith
  have hc' : 0 ≤ C' := hC.trans hc
  calc
    _ ≤ runtimeBound C' A d L n := runtimeBound_mono_constant hc A d L n
    _ ≤ runtimeBound C' A d' L n :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb hd) hc') (by positivity)
    _ ≤ _ := runtimeBound_mono_exponent hc' ha d' L n

theorem polynomial_le (c q L n : ℕ) {A : ℝ} (ha : 0 ≤ A) :
    ((c * (L + 1)^q : ℕ) : ℝ) ≤ runtimeBound c A q L n := by
  have h0 : ((c * (L + 1)^q : ℕ) : ℝ) = runtimeBound c 0 q L n := by
    simp [runtimeBound]
  rw [h0]
  exact runtimeBound_mono_exponent (Nat.cast_nonneg c) ha q L n

theorem word_width_le {n L : ℕ} (good : GoodInput n) (hnL : n ≤ L) :
    SubexpLeafContract.wordWidth n (ell n) (p n) ≤ (L + 1)^2 := by
  simpa only [SubexpLeafContract.wordWidth, SubexpLeafContract.dimension,
    Fintype.card_fin, SubexpPackingParameters.D] using
    SubexpMainCacheBounds.baseWidth_le_square
      ((DyadicParameterBounds.p_le_n good).trans hnL)
      ((DyadicParameterBounds.D_le_n good).trans hnL)

def baseConstant (cfg : Config) (er : ℕ) (C : ℝ) : ℝ :=
  2*C + (8*cfg.k + 5 + helperSize cfg + workRegs er + 1 : ℕ)

def baseDegree (cfg : Config) (d : ℕ) : ℕ := d + 2*cfg.k + 3

def constant (cfg : Config) (er : ℕ) (C : ℝ) : ℝ :=
  7*(50003*(baseConstant cfg er C)^2)^2

def exponent (A : ℝ) : ℝ := 4*(A+3)

def degree (cfg : Config) (d : ℕ) : ℕ := baseDegree cfg d*4

variable {cfg : Config} {er n : ℕ} {hr : 32 ≤ workRegs er} {F : SAT.CNF (Fin n)}

/-- All records and startup costs belong to the same actual boot. The
prefix ceiling is only a proof budget and is not an executed oracle. -/
theorem measured_bound (boot : SubexpMainBoot.Run cfg hr F)
    {C A : ℝ} {d : ℕ} (hC : 1 ≤ C) (hA : 0 ≤ A) (good : GoodInput n)
    (hboot : (SubexpMainBootBounds.totalSteps boot : ℝ) ≤
      runtimeBound C A d (Encoding.formulaBitLength F) n)
    (hcount : (boot.records.length : ℝ) ≤ runtimeBound C A d (Encoding.formulaBitLength F) n) :
    ((SubexpMainBootBounds.totalSteps boot + 5 + RecordPrograms.budget
      (SubexpMainAssembly.leafCost er (helperSize cfg) n (ell n) (p n)
        (SubexpMainPrefixBudget.limit C A d (Encoding.formulaBitLength F) n))
      boot.records : ℕ) : ℝ) ≤
      runtimeBound (constant cfg er C) (exponent A) (degree cfg d)
        (Encoding.formulaBitLength F) n := by
  let L := Encoding.formulaBitLength F
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
  have hbootP : (SubexpMainBootBounds.totalSteps boot : ℝ) ≤ P :=
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
    apply (Nat.cast_le.mpr (SubexpMainBootBounds.record_length boot bits hb)).trans
    apply hsmall (8*cfg.k+5) (2*cfg.k+1)
    · dsimp [K, baseConstant]
      push_cast
      linarith
    · dsimp [q, baseDegree]; omega
  have hwidth : (SubexpLeafContract.wordWidth n (ell n) (p n) : ℝ) ≤ P := by
    apply (Nat.cast_le.mpr (word_width_le good (Encoding.numVariables_le_formulaBitLength F))).trans
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
    (SubexpMainBootBounds.totalSteps boot) boot.records
    (SubexpMainAssembly.leafCost er (helperSize cfg) n (ell n) (p n)
      (SubexpMainPrefixBudget.limit C A d L n)) hQconstant (by positivity : 0 ≤ 2*E)
      (hbootP.trans hPQ) (hcountP.trans hPQ) hvisits
  (convert total using 1; dsimp [constant, exponent, degree, K, E, q, L]; ring_nf)

end SubexponentialSAT.SubexpMainMeasuredBound

end OAI.Algorithms
