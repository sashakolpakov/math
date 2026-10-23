import StickKnots.LowerCertification
import StickKnots.StickUpperCertificate
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Conditional end-to-end asymptotic certificate

This file connects the typed upper and lower certificates to the manuscript's
headline asymptotic statement.  The knot-theoretic and real-algebraic inputs
are packaged as maps and theorems about the actual types used in the proof;
they are not free inequalities between unrelated natural numbers.

Mathlib's global logarithmic Stirling bound is used below to eliminate the
factorials.  The headline statement
`log |K_N| = Theta(N log N)` is then proved with no analytic hypothesis,
using the conservative subfamily `q=2`, `k=floor(N/132)`.

The sharper manuscript coefficient `2/3` is also certified without an
arithmetic hypothesis: for every `c < 2/3`, Lean chooses a sufficiently large
fixed word length `q=q(c)` and checks the complete finite-to-asymptotic
argument.  The logarithmic choice `q_N=floor(log N)` remains useful for the
more precise displayed `-(2/3) N log log N + O(N)` deficit.  That optional
refinement is isolated in `OptimizedDeficitArithmetic` and then composed with
the typed knot-count transfer inside Lean. `ManuscriptArithmetic.lean`
subsequently proves this arithmetic input and exports the refined conclusion
with only the cited geometry, real-algebraic, braid and knot inputs.
-/

namespace StickKnots

open Filter Function Asymptotics

noncomputable section

/-- The manuscript's logarithmic Garside word length. -/
def optimizedWordLength (N : ℕ) : ℕ :=
  ⌊Real.log (N : ℝ)⌋₊

/-- One quarter of the manuscript's strand number `n_N = 4 k_N`. -/
def optimizedQuarterStrands (N : ℕ) : ℕ :=
  (2 * N + 15) / (12 * (optimizedWordLength N + 9))

/-- A deliberately non-optimized linear parameter choice used to certify the
headline `Theta` theorem without any floor/log asymptotic hypothesis. -/
def coarseQuarterStrands (N : ℕ) : ℕ := N / 132

/-- Quarter-strand count for a fixed word length `q`.  Keeping `q` fixed
while letting it grow after the estimate is proved avoids all asymptotics of
the logarithmic floor used by `optimizedQuarterStrands`. -/
def fixedWordQuarterStrands (q N : ℕ) : ℕ :=
  N / (6 * (q + 9))

/-- The exact logarithmic scale whose order of growth is claimed. -/
def knotLogScale (N : ℕ) : ℝ :=
  (N : ℝ) * Real.log (N : ℝ)

/-- The explicit lower logarithm delivered by the certified word count. -/
def optimizedLowerLog (N : ℕ) : ℝ :=
  4 * (optimizedWordLength N : ℝ) *
      Real.log ((optimizedQuarterStrands N).factorial : ℝ) -
    Real.log ((4 * optimizedQuarterStrands N).factorial : ℝ) - Real.log 2

/-- The factorial-free lower envelope obtained from the quarter-family loss
and mathlib's logarithmic Stirling inequality. -/
def optimizedStirlingLowerLog (N : ℕ) : ℝ :=
  ((optimizedWordLength N - 1 : ℕ) : ℝ) *
      (((4 * optimizedQuarterStrands N : ℕ) : ℝ) *
          Real.log (4 * optimizedQuarterStrands N : ℝ) -
        (4 * optimizedQuarterStrands N : ℕ)) -
    9 * (optimizedWordLength N : ℝ) * (optimizedQuarterStrands N : ℝ) *
      Real.log 2 - Real.log 2

/-- Factorial-free lower envelope for `q=2`, `k=floor(N/132)`. -/
def coarseStirlingLowerLog (N : ℕ) : ℝ :=
  4 * (coarseQuarterStrands N : ℝ) *
      Real.log (coarseQuarterStrands N : ℝ) -
    4 * (coarseQuarterStrands N : ℝ) -
    9 * (coarseQuarterStrands N : ℝ) * Real.log 2 - Real.log 2

/-- Factorial-free lower envelope for a fixed word length `q`. -/
def fixedWordStirlingLowerLog (q N : ℕ) : ℝ :=
  ((q - 1 : ℕ) : ℝ) *
      (((4 * fixedWordQuarterStrands q N : ℕ) : ℝ) *
          Real.log (4 * fixedWordQuarterStrands q N : ℝ) -
        (4 * fixedWordQuarterStrands q N : ℕ)) -
    9 * (q : ℝ) * (fixedWordQuarterStrands q N : ℝ) * Real.log 2 -
      Real.log 2

/-- Leading coefficient supplied by the fixed word length `q`. -/
def fixedWordLeadingCoefficient (q : ℕ) : ℝ :=
  4 * ((q - 1 : ℕ) : ℝ) / (6 * (q + 9 : ℕ) : ℝ)

/-- A deliberately generous *scaled* linear-error coefficient in the
elementary fixed-`q` lower estimate.  Multiplication by the fixed denominator
keeps the pointwise proof free of asymptotic division bookkeeping. -/
def fixedWordErrorCoefficient (q : ℕ) : ℝ :=
  4 * ((q - 1 : ℕ) : ℝ) * Real.log (12 * (q + 9 : ℕ) : ℝ) +
    (4 * ((q - 1 : ℕ) : ℝ) + 9 * (q : ℝ) * Real.log 2) +
    4 * ((q - 1 : ℕ) : ℝ) * (6 * (q + 9 : ℕ) : ℝ) +
    (6 * (q + 9 : ℕ) : ℝ) * Real.log 2

/-- The explicit logarithm of the unsliced real-algebraic upper bound. -/
def unslicedUpperLog (factor N : ℕ) : ℝ :=
  Real.log ((3 * N + 1 : ℝ) * (12 * factor * N : ℝ) ^ (3 * N))

/-- The quarter-strand floor has exactly the capacity required by the
Malyutin--Stupakov/Huh--Oh budget calculation. -/
theorem optimizedQuarterStrands_capacity (N : ℕ) :
    3 * ((4 * optimizedQuarterStrands N) * (optimizedWordLength N + 9)) ≤
      2 * N + 15 := by
  calc
    3 * ((4 * optimizedQuarterStrands N) * (optimizedWordLength N + 9)) =
        (12 * (optimizedWordLength N + 9)) *
          ((2 * N + 15) / (12 * (optimizedWordLength N + 9))) := by
      simp only [optimizedQuarterStrands]
      ring
    _ ≤ 2 * N + 15 := Nat.mul_div_le _ _

/-- Hence, on the branch `q_N >= 2`, every knot in the typed lower family
has stick number at most `N`. -/
theorem optimized_longWordStickBudget_le (N : ℕ)
    (hq : 2 ≤ optimizedWordLength N) :
    KnotTransferCertificate.longWordStickBudget
        (optimizedQuarterStrands N) (optimizedWordLength N) ≤ N := by
  have h := wordArcBudget_fits (n := 4 * optimizedQuarterStrands N)
    hq (optimizedQuarterStrands_capacity N)
  exact Nat.div_le_of_le_mul (by
    simpa [KnotTransferCertificate.longWordStickBudget, huhOhStickBudget] using h)

/-- The conservative fixed choice `q=2`, `k=floor(N/132)` fits the same stick
budget with room to spare. -/
theorem coarse_longWordStickBudget_le (N : ℕ) :
    KnotTransferCertificate.longWordStickBudget (coarseQuarterStrands N) 2 ≤ N := by
  have hdiv : 132 * coarseQuarterStrands N ≤ N := by
    simpa [coarseQuarterStrands, Nat.mul_comm] using Nat.div_mul_le_self N 132
  have hcapacity :
      3 * ((4 * coarseQuarterStrands N) * (2 + 9)) ≤ 2 * N + 15 := by
    calc
      3 * ((4 * coarseQuarterStrands N) * (2 + 9)) =
          132 * coarseQuarterStrands N := by ring
      _ ≤ N := hdiv
      _ ≤ 2 * N + 15 := by omega
  have h := wordArcBudget_fits (n := 4 * coarseQuarterStrands N)
    (q := 2) (by omega) hcapacity
  exact Nat.div_le_of_le_mul (by
    simpa [KnotTransferCertificate.longWordStickBudget, huhOhStickBudget] using h)

/-- Every fixed word length uses the same exact stick budget, with
`k = floor(N / (6(q+9)))`. -/
theorem fixedWord_longWordStickBudget_le (q N : ℕ) (hq : 2 ≤ q) :
    KnotTransferCertificate.longWordStickBudget
        (fixedWordQuarterStrands q N) q ≤ N := by
  have hdiv :
      (6 * (q + 9)) * fixedWordQuarterStrands q N ≤ N := by
    simpa [fixedWordQuarterStrands, Nat.mul_comm] using
      Nat.div_mul_le_self N (6 * (q + 9))
  have hcapacity :
      3 * ((4 * fixedWordQuarterStrands q N) * (q + 9)) ≤ 2 * N + 15 := by
    calc
      3 * ((4 * fixedWordQuarterStrands q N) * (q + 9)) =
          2 * ((6 * (q + 9)) * fixedWordQuarterStrands q N) := by ring
      _ ≤ 2 * N := Nat.mul_le_mul_left 2 hdiv
      _ ≤ 2 * N + 15 := Nat.le_add_right _ _
  have h := wordArcBudget_fits (n := 4 * fixedWordQuarterStrands q N)
    hq hcapacity
  exact Nat.div_le_of_le_mul (by
    simpa [KnotTransferCertificate.longWordStickBudget, huhOhStickBudget] using h)

/-- All external mathematics needed uniformly in `N`.

The fields are theorem-shaped and tied to the actual objects:

* `semantic` classifies the actual wall-free polygon space;
* `baroneBasu` bounds every actual degree-four polynomial family;
* `garside` interprets the actual doubly-down--up word type;
* `transfer` is the actual typed Malyutin--Stupakov/Huh--Oh transfer.
-/
structure StickAsymptoticExternalInputs
    (KnotType : Type) (stickNumber : KnotType → ℕ) (factor : ℕ) where
  semantic : ∀ N, StickKnotSemanticInput N KnotType stickNumber
  baroneBasu : DegreeFourComponentTheorem factor
  OrientedKnot : ℕ → ℕ → Type
  garside : ∀ k q, 1 ≤ k → 1 ≤ q → GarsideStageCertificate k q
  transfer : ∀ k q (hk : 1 ≤ k) (hq : 1 ≤ q),
    KnotTransferCertificate (garside k q hk hq) (OrientedKnot k q) KnotType
  transfer_stickNumber : ∀ k q (hk : 1 ≤ k) (hq : 1 ≤ q),
    (transfer k q hk hq).stickNumber = stickNumber

/-- The actual number of knot types with stick number at most `N`. -/
abbrev certifiedKnotCount {KnotType : Type} (stickNumber : KnotType → ℕ)
    (N : ℕ) : ℕ :=
  Nat.card (BoundedStickKnot stickNumber N)

/-- The upper certificate also proves finiteness of the bounded-knot subtype,
which is needed to use `Nat.card` functorially in the lower transfer. -/
theorem boundedStickKnot_finite
    {N factor : ℕ} {KnotType : Type} {stickNumber : KnotType → ℕ}
    (semantic : StickKnotSemanticInput N KnotType stickNumber)
    (baroneBasu : DegreeFourComponentTheorem factor) :
    Finite (BoundedStickKnot stickNumber N) := by
  let components := polygonPathComponentBoundFromBaroneBasu
    (N := N) baroneBasu
  letI : Finite (ZerothHomotopy (Config.WallFreeSpace N)) :=
    components.finiteComponents
  exact Finite.of_surjective semantic.certificate.onPathComponents
    semantic.certificate.onPathComponents_surjective

/-- Inclusion of the property-restricted lower family into the headline
bounded-knot type. -/
def lowerFamilyToBoundedStickKnot
    {N k q : ℕ} {KnotType OrientedKnot : Type}
    {c : GarsideStageCertificate k q}
    (t : KnotTransferCertificate c OrientedKnot KnotType)
    (stickNumber : KnotType → ℕ)
    (hstick : t.stickNumber = stickNumber)
    (hbudget : KnotTransferCertificate.longWordStickBudget k q ≤ N) :
    KnotTransferCertificate.BoundedKnots t → BoundedStickKnot stickNumber N :=
  fun K ↦ ⟨K.1.1, by
    rw [← hstick]
    exact K.1.2.trans hbudget⟩

theorem lowerFamilyToBoundedStickKnot_injective
    {N k q : ℕ} {KnotType OrientedKnot : Type}
    {c : GarsideStageCertificate k q}
    (t : KnotTransferCertificate c OrientedKnot KnotType)
    (stickNumber : KnotType → ℕ)
    (hstick : t.stickNumber = stickNumber)
    (hbudget : KnotTransferCertificate.longWordStickBudget k q ≤ N) :
    Injective (lowerFamilyToBoundedStickKnot t stickNumber hstick hbudget) := by
  intro K L hKL
  have hbase : K.1.1 = L.1.1 :=
    congrArg (fun Z : BoundedStickKnot stickNumber N ↦ Z.1) hKL
  apply Subtype.ext
  exact Subtype.ext hbase

/-- Fully typed finite lower bound for any admissible long-word parameters
whose certified stick budget fits below `N`. -/
theorem certifiedKnotCount_finite_lower_at
    {factor N k q : ℕ} {KnotType : Type} {stickNumber : KnotType → ℕ}
    (inputs : StickAsymptoticExternalInputs KnotType stickNumber factor)
    (hk : 1 ≤ k) (hq : 1 ≤ q)
    (hbudget : KnotTransferCertificate.longWordStickBudget k q ≤ N) :
    (k.factorial ^ 4) ^ q ≤
      2 * (4 * k).factorial * certifiedKnotCount stickNumber N := by
  let c := inputs.garside k q hk hq
  let t := inputs.transfer k q hk hq
  letI : Finite (BoundedStickKnot stickNumber N) :=
    boundedStickKnot_finite (inputs.semantic N) inputs.baroneBasu
  letI : Finite (KnotTransferCertificate.BoundedKnots t) :=
    Finite.of_injective
      (lowerFamilyToBoundedStickKnot t stickNumber
        (inputs.transfer_stickNumber k q hk hq) hbudget)
      (lowerFamilyToBoundedStickKnot_injective t stickNumber
        (inputs.transfer_stickNumber k q hk hq) hbudget)
  have hfamily : Nat.card (KnotTransferCertificate.BoundedKnots t) ≤
      certifiedKnotCount stickNumber N :=
    Nat.card_le_card_of_injective
      (lowerFamilyToBoundedStickKnot t stickNumber
        (inputs.transfer_stickNumber k q hk hq) hbudget)
      (lowerFamilyToBoundedStickKnot_injective t stickNumber
        (inputs.transfer_stickNumber k q hk hq) hbudget)
  calc
    (k.factorial ^ 4) ^ q ≤
        2 * (4 * k).factorial * Nat.card (KnotTransferCertificate.BoundedKnots t) :=
      t.finite_stick_lower_bound
    _ ≤ 2 * (4 * k).factorial * certifiedKnotCount stickNumber N :=
      Nat.mul_le_mul_left _ hfamily

/-- Fully typed finite lower bound at the manuscript's exact logarithmic
parameters.  All endpoint-fiber, orientation, arc-index, and stick-number
logic is derived by `LowerCertification`. -/
theorem certifiedKnotCount_finite_lower
    {factor N : ℕ} {KnotType : Type} {stickNumber : KnotType → ℕ}
    (inputs : StickAsymptoticExternalInputs KnotType stickNumber factor)
    (hq : 2 ≤ optimizedWordLength N)
    (hk : 1 ≤ optimizedQuarterStrands N) :
    (((optimizedQuarterStrands N).factorial ^ 4) ^ optimizedWordLength N) ≤
      2 * (4 * optimizedQuarterStrands N).factorial *
        certifiedKnotCount stickNumber N :=
  certifiedKnotCount_finite_lower_at inputs hk (by omega)
    (optimized_longWordStickBudget_le N hq)

/-- Fully typed finite lower bound for the conservative fixed-`q` family. -/
theorem certifiedKnotCount_coarse_finite_lower
    {factor N : ℕ} {KnotType : Type} {stickNumber : KnotType → ℕ}
    (inputs : StickAsymptoticExternalInputs KnotType stickNumber factor)
    (hk : 1 ≤ coarseQuarterStrands N) :
    ((coarseQuarterStrands N).factorial ^ 4) ^ 2 ≤
      2 * (4 * coarseQuarterStrands N).factorial *
        certifiedKnotCount stickNumber N :=
  certifiedKnotCount_finite_lower_at inputs hk (by omega)
    (coarse_longWordStickBudget_le N)

/-- Fully typed finite lower bound for an arbitrary fixed word length. -/
theorem certifiedKnotCount_fixedWord_finite_lower
    {factor q N : ℕ} {KnotType : Type} {stickNumber : KnotType → ℕ}
    (inputs : StickAsymptoticExternalInputs KnotType stickNumber factor)
    (hq : 2 ≤ q) (hk : 1 ≤ fixedWordQuarterStrands q N) :
    ((fixedWordQuarterStrands q N).factorial ^ 4) ^ q ≤
      2 * (4 * fixedWordQuarterStrands q N).factorial *
        certifiedKnotCount stickNumber N :=
  certifiedKnotCount_finite_lower_at inputs hk (by omega)
    (fixedWord_longWordStickBudget_le q N hq)

theorem certifiedKnotCount_coarse_pos
    {factor N : ℕ} {KnotType : Type} {stickNumber : KnotType → ℕ}
    (inputs : StickAsymptoticExternalInputs KnotType stickNumber factor)
    (hk : 1 ≤ coarseQuarterStrands N) :
    0 < certifiedKnotCount stickNumber N := by
  have h := certifiedKnotCount_coarse_finite_lower inputs hk
  have hleft : 0 < (((coarseQuarterStrands N).factorial ^ 4) ^ 2) :=
    pow_pos (pow_pos (Nat.factorial_pos _) 4) 2
  by_contra hcount
  have hcount0 : certifiedKnotCount stickNumber N = 0 :=
    Nat.eq_zero_of_not_pos hcount
  rw [hcount0, mul_zero] at h
  omega

theorem certifiedKnotCount_fixedWord_pos
    {factor q N : ℕ} {KnotType : Type} {stickNumber : KnotType → ℕ}
    (inputs : StickAsymptoticExternalInputs KnotType stickNumber factor)
    (hq : 2 ≤ q) (hk : 1 ≤ fixedWordQuarterStrands q N) :
    0 < certifiedKnotCount stickNumber N := by
  have h := certifiedKnotCount_fixedWord_finite_lower inputs hq hk
  have hleft :
      0 < (((fixedWordQuarterStrands q N).factorial ^ 4) ^ q) :=
    pow_pos (pow_pos (Nat.factorial_pos _) 4) q
  by_contra hcount
  have hcount0 : certifiedKnotCount stickNumber N = 0 :=
    Nat.eq_zero_of_not_pos hcount
  rw [hcount0, mul_zero] at h
  omega

/-- Mathlib's logarithmic Stirling theorem turns the conservative typed word
count into a completely explicit factorial-free lower bound. -/
theorem coarseStirlingLowerLog_le_log_certifiedKnotCount
    {factor N : ℕ} {KnotType : Type} {stickNumber : KnotType → ℕ}
    (inputs : StickAsymptoticExternalInputs KnotType stickNumber factor)
    (hk : 1 ≤ coarseQuarterStrands N) :
    coarseStirlingLowerLog N ≤
      Real.log (certifiedKnotCount stickNumber N : ℝ) := by
  let k := coarseQuarterStrands N
  have hNat := certifiedKnotCount_coarse_finite_lower inputs hk
  have hcountPos : 0 < certifiedKnotCount stickNumber N :=
    certifiedKnotCount_coarse_pos inputs hk
  have hReal :
      ((((k.factorial ^ 4) ^ 2 : ℕ) : ℝ)) ≤
        (2 : ℝ) * ((4 * k).factorial : ℝ) *
          (certifiedKnotCount stickNumber N : ℝ) := by
    exact_mod_cast hNat
  have hLog := Real.log_le_log
    (by positivity : (0 : ℝ) < ((((k.factorial ^ 4) ^ 2 : ℕ) : ℝ))) hReal
  have hcount : (certifiedKnotCount stickNumber N : ℝ) ≠ 0 := by
    exact_mod_cast hcountPos.ne'
  norm_num only [Nat.cast_pow] at hLog
  rw [Real.log_pow, Real.log_pow,
    Real.log_mul (by positivity :
      (2 : ℝ) * ((4 * k).factorial : ℝ) ≠ 0) hcount,
    Real.log_mul (by positivity : (2 : ℝ) ≠ 0)
      (by positivity : ((4 * k).factorial : ℝ) ≠ 0)] at hLog
  norm_num at hLog
  have hquarter := log_factorial_four_mul_le_log_quarter_factorials k
  norm_num only [Nat.cast_mul] at hquarter
  have hmiddle :
      4 * Real.log (k.factorial : ℝ) -
          9 * (k : ℝ) * Real.log 2 - Real.log 2 ≤
        8 * Real.log (k.factorial : ℝ) -
          Real.log ((4 * k).factorial : ℝ) - Real.log 2 := by
    nlinarith
  have hStirling := Stirling.le_log_factorial_stirling (show k ≠ 0 by omega)
  have hlogk : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hk)
  have hlog2pi : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hcoarse :
      (k : ℝ) * Real.log (k : ℝ) - k ≤
        Real.log (k.factorial : ℝ) := by
    nlinarith
  have hfirst :
      4 * (k : ℝ) * Real.log (k : ℝ) - 4 * k -
          9 * k * Real.log 2 - Real.log 2 ≤
        4 * Real.log (k.factorial : ℝ) -
          9 * k * Real.log 2 - Real.log 2 := by
    nlinarith
  change coarseStirlingLowerLog N ≤
    Real.log (certifiedKnotCount stickNumber N : ℝ)
  change
    4 * (k : ℝ) * Real.log (k : ℝ) - 4 * k -
        9 * k * Real.log 2 - Real.log 2 ≤
      Real.log (certifiedKnotCount stickNumber N : ℝ)
  exact hfirst.trans (hmiddle.trans (by nlinarith [hLog]))

/-- Mathlib's global Stirling inequality turns the typed fixed-`q` word
count into the explicit factorial-free lower envelope. -/
theorem fixedWordStirlingLowerLog_le_log_certifiedKnotCount
    {factor q N : ℕ} {KnotType : Type} {stickNumber : KnotType → ℕ}
    (inputs : StickAsymptoticExternalInputs KnotType stickNumber factor)
    (hq : 2 ≤ q) (hk : 1 ≤ fixedWordQuarterStrands q N) :
    fixedWordStirlingLowerLog q N ≤
      Real.log (certifiedKnotCount stickNumber N : ℝ) := by
  let k := fixedWordQuarterStrands q N
  have hNat := certifiedKnotCount_fixedWord_finite_lower inputs hq hk
  have hcountPos : 0 < certifiedKnotCount stickNumber N :=
    certifiedKnotCount_fixedWord_pos inputs hq hk
  have hReal :
      ((((k.factorial ^ 4) ^ q : ℕ) : ℝ)) ≤
        (2 : ℝ) * ((4 * k).factorial : ℝ) *
          (certifiedKnotCount stickNumber N : ℝ) := by
    exact_mod_cast hNat
  have hLog := Real.log_le_log
    (by positivity : (0 : ℝ) < ((((k.factorial ^ 4) ^ q : ℕ) : ℝ))) hReal
  have hcount : (certifiedKnotCount stickNumber N : ℝ) ≠ 0 := by
    exact_mod_cast hcountPos.ne'
  norm_num only [Nat.cast_pow] at hLog
  rw [Real.log_pow, Real.log_pow,
    Real.log_mul (by positivity :
      (2 : ℝ) * ((4 * k).factorial : ℝ) ≠ 0) hcount,
    Real.log_mul (by positivity : (2 : ℝ) ≠ 0)
      (by positivity : ((4 * k).factorial : ℝ) ≠ 0)] at hLog
  norm_num at hLog
  have hquarter := log_factorial_four_mul_le_log_quarter_factorials k
  have hquarterMul := mul_le_mul_of_nonneg_left hquarter
    (show (0 : ℝ) ≤ q by positivity)
  have hqsub : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    norm_num
  have hfactorial :
      ((q - 1 : ℕ) : ℝ) * Real.log ((4 * k).factorial : ℝ) -
          9 * (q : ℝ) * (k : ℝ) * Real.log 2 - Real.log 2 ≤
        4 * (q : ℝ) * Real.log (k.factorial : ℝ) -
          Real.log ((4 * k).factorial : ℝ) - Real.log 2 := by
    norm_num only [Nat.cast_mul] at hquarterMul
    rw [hqsub]
    nlinarith
  have h4k : 4 * k ≠ 0 := by omega
  have hStirling := Stirling.le_log_factorial_stirling h4k
  have hlog4k : 0 ≤ Real.log ((4 * k : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 4 * k by omega))
  have hlog2pi : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hcoarse :
      ((4 * k : ℕ) : ℝ) * Real.log ((4 * k : ℕ) : ℝ) -
          ((4 * k : ℕ) : ℝ) ≤
        Real.log ((4 * k).factorial : ℝ) := by
    norm_num only [Nat.cast_mul] at hStirling hlog4k ⊢
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hcoarse
    (show (0 : ℝ) ≤ ((q - 1 : ℕ) : ℝ) by positivity)
  have hfinal :
      ((q - 1 : ℕ) : ℝ) *
            (((4 * k : ℕ) : ℝ) * Real.log ((4 * k : ℕ) : ℝ) -
              ((4 * k : ℕ) : ℝ)) -
          9 * (q : ℝ) * (k : ℝ) * Real.log 2 - Real.log 2 ≤
        4 * (q : ℝ) * Real.log (k.factorial : ℝ) -
          Real.log ((4 * k).factorial : ℝ) - Real.log 2 :=
    (sub_le_sub_right
      (sub_le_sub_right hmul (9 * (q : ℝ) * (k : ℝ) * Real.log 2))
      (Real.log 2)).trans hfactorial
  simpa [fixedWordStirlingLowerLog, k] using
    hfinal.trans (by nlinarith [hLog])

/-- Typed finite upper bound at the same headline count. -/
theorem certifiedKnotCount_finite_upper
    {factor N : ℕ} {KnotType : Type} {stickNumber : KnotType → ℕ}
    (inputs : StickAsymptoticExternalInputs KnotType stickNumber factor)
    (hN : 5 ≤ N) :
    (certifiedKnotCount stickNumber N : ℝ) ≤
      (3 * N + 1 : ℝ) * (12 * factor * N : ℝ) ^ (3 * N) :=
  boundedStickKnot_count_le_unsliced hN (inputs.semantic N) inputs.baroneBasu

/-- The typed lower construction supplies an actual bounded knot, so the
headline cardinality is positive (and taking its logarithm is legitimate). -/
theorem certifiedKnotCount_pos
    {factor N : ℕ} {KnotType : Type} {stickNumber : KnotType → ℕ}
    (inputs : StickAsymptoticExternalInputs KnotType stickNumber factor)
    (hq : 2 ≤ optimizedWordLength N)
    (hk : 1 ≤ optimizedQuarterStrands N) :
    0 < certifiedKnotCount stickNumber N := by
  have h := certifiedKnotCount_finite_lower inputs hq hk
  have hleft :
      0 < (((optimizedQuarterStrands N).factorial ^ 4) ^ optimizedWordLength N) :=
    pow_pos (pow_pos (Nat.factorial_pos _) 4) _
  by_contra hcount
  have hcount0 : certifiedKnotCount stickNumber N = 0 :=
    Nat.eq_zero_of_not_pos hcount
  rw [hcount0, mul_zero] at h
  omega

/-- Exact logarithmic consequence of the typed finite lower certificate. -/
theorem optimizedLowerLog_le_log_certifiedKnotCount
    {factor N : ℕ} {KnotType : Type} {stickNumber : KnotType → ℕ}
    (inputs : StickAsymptoticExternalInputs KnotType stickNumber factor)
    (hq : 2 ≤ optimizedWordLength N)
    (hk : 1 ≤ optimizedQuarterStrands N) :
    optimizedLowerLog N ≤
      Real.log (certifiedKnotCount stickNumber N : ℝ) := by
  have hNat := certifiedKnotCount_finite_lower inputs hq hk
  have hReal :
      ((((optimizedQuarterStrands N).factorial ^ 4) ^
          optimizedWordLength N : ℕ) : ℝ) ≤
        (2 : ℝ) * ((4 * optimizedQuarterStrands N).factorial : ℝ) *
          (certifiedKnotCount stickNumber N : ℝ) := by
    exact_mod_cast hNat
  have hLog := Real.log_le_log (by positivity :
      (0 : ℝ) < ((((optimizedQuarterStrands N).factorial ^ 4) ^
        optimizedWordLength N : ℕ) : ℝ)) hReal
  have hcount : (certifiedKnotCount stickNumber N : ℝ) ≠ 0 := by
    exact_mod_cast (certifiedKnotCount_pos inputs hq hk).ne'
  norm_num only [Nat.cast_pow] at hLog
  rw [Real.log_pow, Real.log_pow,
    Real.log_mul (by positivity :
      (2 : ℝ) * ((4 * optimizedQuarterStrands N).factorial : ℝ) ≠ 0) hcount,
    Real.log_mul (by positivity : (2 : ℝ) ≠ 0)
      (by positivity : ((4 * optimizedQuarterStrands N).factorial : ℝ) ≠ 0)]
    at hLog
  norm_num at hLog
  unfold optimizedLowerLog
  nlinarith

/-- Mathlib's global Stirling inequality and the Lean-verified exponential
loss `(4k)! <= 2^(9k) (k!)^4` remove every factorial from the lower envelope.
This is the analytic heart of the `2/3` calculation before the remaining
floor/log parameter asymptotics. -/
theorem optimizedStirlingLowerLog_le_optimizedLowerLog
    {N : ℕ} (hq : 2 ≤ optimizedWordLength N)
    (hk : 1 ≤ optimizedQuarterStrands N) :
    optimizedStirlingLowerLog N ≤ optimizedLowerLog N := by
  let q := optimizedWordLength N
  let k := optimizedQuarterStrands N
  have hquarter := log_factorial_four_mul_le_log_quarter_factorials k
  have hquarterMul := mul_le_mul_of_nonneg_left hquarter (show (0 : ℝ) ≤ q by positivity)
  have hqsub : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    norm_num
  have hfactorial :
      ((q - 1 : ℕ) : ℝ) * Real.log ((4 * k).factorial : ℝ) -
          9 * (q : ℝ) * (k : ℝ) * Real.log 2 - Real.log 2 ≤
        4 * (q : ℝ) * Real.log (k.factorial : ℝ) -
          Real.log ((4 * k).factorial : ℝ) - Real.log 2 := by
    norm_num only [Nat.cast_mul] at hquarterMul
    rw [hqsub]
    nlinarith
  have h4k : 4 * k ≠ 0 := by omega
  have hStirling := Stirling.le_log_factorial_stirling h4k
  have hlog4k : 0 ≤ Real.log ((4 * k : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 4 * k by omega))
  have hlog2pi : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hcoarse :
      ((4 * k : ℕ) : ℝ) * Real.log ((4 * k : ℕ) : ℝ) -
          ((4 * k : ℕ) : ℝ) ≤
        Real.log ((4 * k).factorial : ℝ) := by
    norm_num only [Nat.cast_mul] at hStirling hlog4k ⊢
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hcoarse
    (show (0 : ℝ) ≤ ((q - 1 : ℕ) : ℝ) by positivity)
  have hfinal :
    ((q - 1 : ℕ) : ℝ) *
          (((4 * k : ℕ) : ℝ) * Real.log ((4 * k : ℕ) : ℝ) -
            ((4 * k : ℕ) : ℝ)) -
        9 * (q : ℝ) * (k : ℝ) * Real.log 2 - Real.log 2 ≤
      4 * (q : ℝ) * Real.log (k.factorial : ℝ) -
        Real.log ((4 * k).factorial : ℝ) - Real.log 2 :=
    (sub_le_sub_right
    (sub_le_sub_right hmul (9 * (q : ℝ) * (k : ℝ) * Real.log 2))
      (Real.log 2)).trans hfactorial
  simpa [optimizedStirlingLowerLog, optimizedLowerLog, q, k, Nat.cast_mul] using hfinal

/-- The fully factorial-free finite lower logarithmic bound. -/
theorem optimizedStirlingLowerLog_le_log_certifiedKnotCount
    {factor N : ℕ} {KnotType : Type} {stickNumber : KnotType → ℕ}
    (inputs : StickAsymptoticExternalInputs KnotType stickNumber factor)
    (hq : 2 ≤ optimizedWordLength N)
    (hk : 1 ≤ optimizedQuarterStrands N) :
    optimizedStirlingLowerLog N ≤
      Real.log (certifiedKnotCount stickNumber N : ℝ) :=
  (optimizedStirlingLowerLog_le_optimizedLowerLog hq hk).trans
    (optimizedLowerLog_le_log_certifiedKnotCount inputs hq hk)

/-- Exact logarithmic consequence of the real-algebraic finite upper
certificate. -/
theorem log_certifiedKnotCount_le_unslicedUpperLog
    {factor N : ℕ} {KnotType : Type} {stickNumber : KnotType → ℕ}
    (inputs : StickAsymptoticExternalInputs KnotType stickNumber factor)
    (hN : 5 ≤ N) (hq : 2 ≤ optimizedWordLength N)
    (hk : 1 ≤ optimizedQuarterStrands N) :
    Real.log (certifiedKnotCount stickNumber N : ℝ) ≤
      unslicedUpperLog factor N := by
  exact Real.log_le_log
    (by exact_mod_cast certifiedKnotCount_pos inputs hq hk)
    (certifiedKnotCount_finite_upper inputs hN)

/-- The manuscript's finite logarithmic sandwich, now expressed entirely in
terms of the actual bounded-knot cardinality and the two explicit numerical
envelopes. -/
theorem certifiedKnotCount_log_sandwich
    {factor N : ℕ} {KnotType : Type} {stickNumber : KnotType → ℕ}
    (inputs : StickAsymptoticExternalInputs KnotType stickNumber factor)
    (hN : 5 ≤ N) (hq : 2 ≤ optimizedWordLength N)
    (hk : 1 ≤ optimizedQuarterStrands N) :
    optimizedLowerLog N ≤
        Real.log (certifiedKnotCount stickNumber N : ℝ) ∧
      Real.log (certifiedKnotCount stickNumber N : ℝ) ≤
        unslicedUpperLog factor N :=
  ⟨optimizedLowerLog_le_log_certifiedKnotCount inputs hq hk,
    log_certifiedKnotCount_le_unslicedUpperLog inputs hN hq hk⟩

/-- The explicit unsliced upper logarithm is nonnegative once both `factor`
and `N` are positive. -/
theorem unslicedUpperLog_nonneg {factor N : ℕ}
    (hfactor : 1 ≤ factor) (hN : 1 ≤ N) :
    0 ≤ unslicedUpperLog factor N := by
  apply Real.log_nonneg
  have hfactorR : (1 : ℝ) ≤ factor := by exact_mod_cast hfactor
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hfirst : (1 : ℝ) ≤ 3 * (N : ℝ) + 1 := by nlinarith
  have hbase : (1 : ℝ) ≤ 12 * (factor : ℝ) * (N : ℝ) := by
    calc
      (1 : ℝ) ≤ 12 * 1 * 1 := by norm_num
      _ ≤ 12 * (factor : ℝ) * (N : ℝ) := by gcongr
  have hpow : (1 : ℝ) ≤ (12 * (factor : ℝ) * (N : ℝ)) ^ (3 * N) :=
    one_le_pow₀ hbase
  nlinarith [mul_le_mul hfirst hpow (by positivity) (by positivity)]

/-- Elementary pointwise `O(N log N)` estimate for the actual upper
envelope.  This removes the upper asymptotic analysis from the external proof
boundary. -/
theorem unslicedUpperLog_le_eight_scale {factor N : ℕ}
    (hfactor : 1 ≤ factor) (hN : max 4 (12 * factor) ≤ N) :
    unslicedUpperLog factor N ≤ 8 * knotLogScale N := by
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hfactorN : 12 * factor ≤ N := (le_max_right _ _).trans hN
  have hfirstNat : 3 * N + 1 ≤ N * N := by nlinarith
  have hbaseNat : 12 * factor * N ≤ N * N :=
    Nat.mul_le_mul_right N hfactorN
  have hfirstReal : 3 * (N : ℝ) + 1 ≤ (N : ℝ) * (N : ℝ) := by
    exact_mod_cast hfirstNat
  have hbaseReal : 12 * (factor : ℝ) * (N : ℝ) ≤ (N : ℝ) * (N : ℝ) := by
    exact_mod_cast hbaseNat
  have hlogFirst := Real.log_le_log
    (by positivity : (0 : ℝ) < 3 * (N : ℝ) + 1) hfirstReal
  have hlogBase := Real.log_le_log
    (by positivity : (0 : ℝ) < 12 * (factor : ℝ) * (N : ℝ)) hbaseReal
  rw [show (N : ℝ) * (N : ℝ) = (N : ℝ) ^ 2 by ring,
    Real.log_pow] at hlogFirst hlogBase
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  unfold unslicedUpperLog knotLogScale
  rw [Real.log_mul
      (by positivity : (3 * N + 1 : ℝ) ≠ 0)
      (by positivity : (12 * factor * N : ℝ) ^ (3 * N) ≠ 0),
    Real.log_pow]
  norm_num only [Nat.cast_mul] at hlogFirst hlogBase ⊢
  nlinarith

/-- The explicit real-algebraic upper logarithm is `O(N log N)`, proved
inside Lean rather than supplied as an asymptotic hypothesis. -/
theorem unslicedUpperLog_isBigO (factor : ℕ) (hfactor : 1 ≤ factor) :
    (unslicedUpperLog factor) =O[atTop] knotLogScale := by
  apply IsBigO.of_bound 8
  filter_upwards [eventually_ge_atTop (max 4 (12 * factor))] with N hN
  change |unslicedUpperLog factor N| ≤ 8 * |knotLogScale N|
  rw [
    abs_of_nonneg (unslicedUpperLog_nonneg hfactor (by omega)),
    show knotLogScale N = (N : ℝ) * Real.log (N : ℝ) by rfl,
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg N) (Real.log_natCast_nonneg N))]
  exact unslicedUpperLog_le_eight_scale hfactor hN

/-- The logarithmic word length tends to infinity.  This use of mathlib's
real logarithm and natural-floor limit discharges the eventual `q_N >= 2`
side condition internally. -/
theorem optimizedWordLength_tendsto_atTop :
    Tendsto optimizedWordLength atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem eventually_two_le_optimizedWordLength :
    ∀ᶠ N in atTop, 2 ≤ optimizedWordLength N :=
  optimizedWordLength_tendsto_atTop.eventually_ge_atTop 2

/-- The optimized quarter-strand floor is eventually positive.  This is
proved from mathlib's `log x = o(x)` theorem, so it is not part of the
remaining `2/3` refinement hypothesis. -/
theorem eventually_one_le_optimizedQuarterStrands :
    ∀ᶠ N in atTop, 1 ≤ optimizedQuarterStrands N := by
  have hLittle :
      (fun N : ℕ ↦ Real.log (N : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have hbound := (isLittleO_iff_nat_mul_le.mp hLittle) 12
  filter_upwards [hbound, eventually_ge_atTop 93] with N hlog hN
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Real.log_natCast_nonneg N),
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg N)] at hlog
  norm_num at hlog
  have hfloor : (optimizedWordLength N : ℝ) ≤ Real.log (N : ℝ) := by
    exact Nat.floor_le (Real.log_natCast_nonneg N)
  have hfloor12 :
      12 * (optimizedWordLength N : ℝ) ≤ 12 * Real.log (N : ℝ) :=
    mul_le_mul_of_nonneg_left hfloor (by norm_num)
  have hNreal : (93 : ℝ) ≤ N := by exact_mod_cast hN
  have hslack : (N : ℝ) + 108 ≤ 2 * (N : ℝ) + 15 := by
    nlinarith
  have hdenReal :
      (12 * (optimizedWordLength N + 9) : ℕ) ≤ (2 * N + 15 : ℕ) := by
    exact_mod_cast (show
      (12 : ℝ) * ((optimizedWordLength N : ℝ) + 9) ≤
        2 * (N : ℝ) + 15 by nlinarith)
  dsimp [optimizedQuarterStrands]
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 12 * (optimizedWordLength N + 9))).2
  simpa using hdenReal

/-- The comparison scale itself tends to infinity. -/
theorem knotLogScale_tendsto_atTop : Tendsto knotLogScale atTop atTop := by
  exact tendsto_natCast_atTop_atTop.atTop_mul_atTop₀
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- A coarse but fully explicit positive-coefficient estimate.  The large
constant is intentional: it keeps all floor arithmetic elementary while
retaining the decisive `N log N` order. -/
theorem one_div_264_scale_le_coarseStirlingLowerLog
    {N : ℕ} (hN : 132 * 264 ≤ N)
    (hlog : (264 : ℝ) * (4 + 10 * Real.log 2) ≤ Real.log (N : ℝ)) :
    (1 / 264 : ℝ) * knotLogScale N ≤ coarseStirlingLowerLog N := by
  let k := coarseQuarterStrands N
  have hk264 : 264 ≤ k := by
    dsimp [k, coarseQuarterStrands]
    omega
  have hkpos : 0 < k := by omega
  have hNk : N ≤ 264 * k := by
    dsimp [k, coarseQuarterStrands]
    omega
  have hkN : k ≤ N := by
    dsimp [k, coarseQuarterStrands]
    exact Nat.div_le_self N 132
  have hNkk : N ≤ k * k := by nlinarith
  have hNpos : 0 < N := by omega
  have hNkkR : (N : ℝ) ≤ (k : ℝ) * (k : ℝ) := by
    exact_mod_cast hNkk
  have hlogSq := Real.log_le_log (by exact_mod_cast hNpos) hNkkR
  rw [show (k : ℝ) * (k : ℝ) = (k : ℝ) ^ 2 by ring,
    Real.log_pow] at hlogSq
  norm_num at hlogSq
  have hlogNnonneg : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hlogknonneg : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega))
  have hkLower : (N : ℝ) / 264 ≤ k := by
    have hNkR : (N : ℝ) ≤ 264 * k := by exact_mod_cast hNk
    nlinarith
  have hlogLower : Real.log (N : ℝ) / 2 ≤ Real.log (k : ℝ) := by
    nlinarith
  have hprod := mul_le_mul hkLower hlogLower
    (by positivity : 0 ≤ Real.log (N : ℝ) / 2)
    (by positivity : 0 ≤ (k : ℝ))
  have hleading :
      (N : ℝ) * Real.log (N : ℝ) / 132 ≤
        4 * (k : ℝ) * Real.log (k : ℝ) := by
    nlinarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hkNR : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hcoeff : 0 ≤ (4 : ℝ) + 9 * Real.log 2 := by positivity
  have herr₁ := mul_le_mul_of_nonneg_left hkNR hcoeff
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog2N : Real.log 2 ≤ Real.log 2 * (N : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hNOne hlog2
  have herr :
      4 * (k : ℝ) + 9 * k * Real.log 2 + Real.log 2 ≤
        (4 + 10 * Real.log 2) * (N : ℝ) := by
    nlinarith
  have herrorScale :
      (4 + 10 * Real.log 2) * (N : ℝ) ≤
        (N : ℝ) * Real.log (N : ℝ) / 264 := by
    have hmul := mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg N)
    nlinarith
  change (1 / 264 : ℝ) * ((N : ℝ) * Real.log (N : ℝ)) ≤
    4 * (k : ℝ) * Real.log (k : ℝ) - 4 * k -
      9 * k * Real.log 2 - Real.log 2
  nlinarith

/-- The conservative lower envelope eventually dominates a fixed positive
multiple of `N log N`; unlike the optimized `2/3` refinement, this theorem has
no external asymptotic-arithmetic hypothesis. -/
theorem eventually_one_div_264_scale_le_coarseStirlingLowerLog :
    ∀ᶠ N in atTop,
      (1 / 264 : ℝ) * knotLogScale N ≤ coarseStirlingLowerLog N := by
  have hlog : ∀ᶠ N : ℕ in atTop,
      (264 : ℝ) * (4 + 10 * Real.log 2) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop (132 * 264), hlog] with N hN hlogN
  exact one_div_264_scale_le_coarseStirlingLowerLog hN hlogN

/-- Pointwise fixed-word estimate.  Its hypothesis is an explicit threshold
on `log N`; no limiting statement or floor asymptotic is assumed. -/
theorem coefficient_scale_le_fixedWordStirlingLowerLog
    {q N : ℕ} {c : ℝ} (hq : 2 ≤ q)
    (hN : 2 * (6 * (q + 9)) ≤ N)
    (hgap : fixedWordErrorCoefficient q ≤
      (4 * ((q - 1 : ℕ) : ℝ) -
        (6 * (q + 9 : ℕ) : ℝ) * c) * Real.log (N : ℝ)) :
    c * knotLogScale N ≤ fixedWordStirlingLowerLog q N := by
  let D : ℕ := 6 * (q + 9)
  let k : ℕ := fixedWordQuarterStrands q N
  let A : ℝ := 4 * ((q - 1 : ℕ) : ℝ)
  let C : ℝ := Real.log ((2 * D : ℕ) : ℝ)
  let E : ℝ := A + 9 * (q : ℝ) * Real.log 2
  have hD : 0 < D := by dsimp [D]; omega
  have hNpos : 0 < N := by omega
  have hk : 1 ≤ k := by
    dsimp [k, fixedWordQuarterStrands, D]
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 6 * (q + 9))).2
    omega
  have hDk : D * k ≤ N := by
    dsimp [k, fixedWordQuarterStrands, D]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self N (6 * (q + 9))
  have hmod : N % D < D := Nat.mod_lt N hD
  have hdecomp : D * (N / D) + N % D = N := Nat.div_add_mod N D
  have hkdef : k = N / D := by rfl
  have hNle : N ≤ D * k + D := by
    rw [hkdef]
    calc
      N = D * (N / D) + N % D := hdecomp.symm
      _ ≤ D * (N / D) + D :=
        Nat.add_le_add_left (Nat.le_of_lt hmod) _
  have hD_le_Dk : D ≤ D * k := by
    simpa only [mul_one] using Nat.mul_le_mul_left D hk
  have hN2Dk : N ≤ (2 * D) * k := by
    rw [show (2 * D) * k = D * k + D * k by ring]
    exact hNle.trans (Nat.add_le_add_left hD_le_Dk (D * k))
  have hN2D : 2 * D ≤ N := by simpa [D] using hN
  have hN2DReal : ((2 * D : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2D
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * D by omega))
  have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hx : 0 ≤ Real.log (N : ℝ) - C := by
    have hlog := Real.log_le_log
      (by exact_mod_cast (show 0 < 2 * D by omega)) hN2DReal
    exact sub_nonneg.2 hlog
  have hN2DkReal : (N : ℝ) ≤ ((2 * D : ℕ) : ℝ) * (k : ℝ) := by
    exact_mod_cast hN2Dk
  have hlogProduct := Real.log_le_log (by exact_mod_cast hNpos) hN2DkReal
  rw [Real.log_mul
      (by exact_mod_cast (show (2 * D : ℕ) ≠ 0 by omega))
      (by exact_mod_cast (show k ≠ 0 by omega))] at hlogProduct
  have hlogk : Real.log (N : ℝ) - C ≤ Real.log (k : ℝ) := by
    dsimp [C]
    linarith
  have hlog4k : Real.log (k : ℝ) ≤ Real.log ((4 * k : ℕ) : ℝ) := by
    apply Real.log_le_log (by exact_mod_cast (show 0 < k by omega))
    exact_mod_cast (show k ≤ 4 * k by omega)
  have hlogLower : Real.log (N : ℝ) - C ≤
      Real.log ((4 * k : ℕ) : ℝ) := hlogk.trans hlog4k
  have hNminusD : (N : ℝ) - (D : ℝ) ≤ (D : ℝ) * (k : ℝ) := by
    have hNleReal : (N : ℝ) ≤ (D : ℝ) * (k : ℝ) + (D : ℝ) := by
      exact_mod_cast hNle
    linarith
  have hleadFloor := mul_le_mul_of_nonneg_right hNminusD hx
  have hleadLog := mul_le_mul_of_nonneg_left hlogLower
    (mul_nonneg (Nat.cast_nonneg D) (Nat.cast_nonneg k))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hleadFloorA := mul_le_mul_of_nonneg_left hleadFloor hA
  have hleadLogA := mul_le_mul_of_nonneg_left hleadLog hA
  have hlead :
      A * ((N : ℝ) - D) * (Real.log (N : ℝ) - C) ≤
        (D : ℝ) * (A * (k : ℝ) * Real.log ((4 * k : ℕ) : ℝ)) := by
    nlinarith
  norm_num only [Nat.cast_mul] at hlead
  have hE : 0 ≤ E := by
    dsimp [E, A]
    positivity
  have hDkReal : (D : ℝ) * (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hDk
  have herror := mul_le_mul_of_nonneg_left hDkReal hE
  have hlogN_le_N : Real.log (N : ℝ) ≤ (N : ℝ) :=
    (Real.log_le_sub_one_of_pos (by exact_mod_cast hNpos)).trans (by linarith)
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlast := mul_le_mul_of_nonneg_left hNOne
    (mul_nonneg (Nat.cast_nonneg D) hlog2)
  have hADlog := mul_le_mul_of_nonneg_left hlogN_le_N
    (mul_nonneg hA (Nat.cast_nonneg D))
  have hADC : 0 ≤ A * (D : ℝ) * C := mul_nonneg
    (mul_nonneg hA (Nat.cast_nonneg D)) hC_nonneg
  have hfixedEq : fixedWordStirlingLowerLog q N =
      A * (k : ℝ) * Real.log (4 * (k : ℝ)) - E * (k : ℝ) - Real.log 2 := by
    dsimp [fixedWordStirlingLowerLog, A, E, k]
    norm_num only [Nat.cast_mul]
    ring
  have herrorCoeffEq : fixedWordErrorCoefficient q =
      A * C + E + A * (D : ℝ) + (D : ℝ) * Real.log 2 := by
    dsimp [fixedWordErrorCoefficient, A, C, D, E]
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    ring_nf
  have herror' : (D : ℝ) * (E * (k : ℝ)) ≤ E * (N : ℝ) := by
    calc
      (D : ℝ) * (E * (k : ℝ)) = E * ((D : ℝ) * (k : ℝ)) := by ring
      _ ≤ E * (N : ℝ) := herror
  have hstep₁ :
      A * ((N : ℝ) - D) * (Real.log (N : ℝ) - C) - E * (N : ℝ) -
          (D : ℝ) * Real.log 2 ≤
        (D : ℝ) *
          (A * (k : ℝ) * Real.log (4 * (k : ℝ)) - E * (k : ℝ) -
            Real.log 2) := by
    have hsub := sub_le_sub hlead herror'
    have hsubLog := sub_le_sub_right hsub ((D : ℝ) * Real.log 2)
    calc
      A * ((N : ℝ) - D) * (Real.log (N : ℝ) - C) - E * (N : ℝ) -
          (D : ℝ) * Real.log 2 ≤
        (D : ℝ) * (A * (k : ℝ) * Real.log (4 * (k : ℝ))) -
          (D : ℝ) * (E * (k : ℝ)) - (D : ℝ) * Real.log 2 := hsubLog
      _ = (D : ℝ) *
          (A * (k : ℝ) * Real.log (4 * (k : ℝ)) - E * (k : ℝ) -
            Real.log 2) := by ring
  have hstep₂ :
      A * (N : ℝ) * Real.log (N : ℝ) - A * C * (N : ℝ) -
          A * (D : ℝ) * (N : ℝ) - E * (N : ℝ) -
          (D : ℝ) * Real.log 2 ≤
        A * ((N : ℝ) - D) * (Real.log (N : ℝ) - C) - E * (N : ℝ) -
          (D : ℝ) * Real.log 2 := by
    linarith [hADlog, hADC]
  have hstep₃ :
      A * (N : ℝ) * Real.log (N : ℝ) -
          (A * C + E + A * (D : ℝ) + (D : ℝ) * Real.log 2) * (N : ℝ) ≤
        A * (N : ℝ) * Real.log (N : ℝ) - A * C * (N : ℝ) -
          A * (D : ℝ) * (N : ℝ) - E * (N : ℝ) -
          (D : ℝ) * Real.log 2 := by
    linarith [hlast]
  have hscaled :
      (D : ℝ) * fixedWordStirlingLowerLog q N ≥
        A * (N : ℝ) * Real.log (N : ℝ) -
          fixedWordErrorCoefficient q * (N : ℝ) := by
    rw [hfixedEq, herrorCoeffEq]
    exact hstep₃.trans (hstep₂.trans hstep₁)
  have hgap' : fixedWordErrorCoefficient q * (N : ℝ) ≤
      (4 * ((q - 1 : ℕ) : ℝ) - (D : ℝ) * c) *
        Real.log (N : ℝ) * (N : ℝ) := by
    have := mul_le_mul_of_nonneg_right hgap (Nat.cast_nonneg N)
    simpa [D] using this
  have hDposReal : (0 : ℝ) < D := by exact_mod_cast hD
  change c * ((N : ℝ) * Real.log (N : ℝ)) ≤
    fixedWordStirlingLowerLog q N
  have hmul :
      (D : ℝ) * (c * ((N : ℝ) * Real.log (N : ℝ))) ≤
        (D : ℝ) * fixedWordStirlingLowerLog q N := by
    calc
      (D : ℝ) * (c * ((N : ℝ) * Real.log (N : ℝ))) =
          A * (N : ℝ) * Real.log (N : ℝ) -
            (4 * ((q - 1 : ℕ) : ℝ) - (D : ℝ) * c) *
              Real.log (N : ℝ) * (N : ℝ) := by
        dsimp [A]
        ring
      _ ≤ A * (N : ℝ) * Real.log (N : ℝ) -
          fixedWordErrorCoefficient q * (N : ℝ) :=
        sub_le_sub_left hgap' _
      _ ≤ (D : ℝ) * fixedWordStirlingLowerLog q N := hscaled
  exact le_of_mul_le_mul_left hmul hDposReal

/-- For a fixed word length, every coefficient below its explicit leading
coefficient is eventually delivered by the typed knot family. -/
theorem eventually_coefficient_lower_bound_of_fixedWord
    {factor q : ℕ} {KnotType : Type} {stickNumber : KnotType → ℕ}
    (inputs : StickAsymptoticExternalInputs KnotType stickNumber factor)
    (hq : 2 ≤ q) {c : ℝ} (hc : c < fixedWordLeadingCoefficient q) :
    ∀ᶠ N in atTop,
      c * knotLogScale N ≤
        Real.log (certifiedKnotCount stickNumber N : ℝ) := by
  let D : ℕ := 6 * (q + 9)
  let gap : ℝ := 4 * ((q - 1 : ℕ) : ℝ) - (D : ℝ) * c
  have hD : (0 : ℝ) < D := by dsimp [D]; positivity
  have hgap : 0 < gap := by
    have hratio : c <
        4 * ((q - 1 : ℕ) : ℝ) / (D : ℝ) := by
      simpa [fixedWordLeadingCoefficient, D] using hc
    exact sub_pos.2 (by simpa [mul_comm] using (lt_div_iff₀ hD).mp hratio)
  have hlog : ∀ᶠ N : ℕ in atTop,
      fixedWordErrorCoefficient q / gap ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop (2 * D), hlog] with N hN hlogN
  have hthreshold : fixedWordErrorCoefficient q ≤
      gap * Real.log (N : ℝ) := by
    simpa [mul_comm] using (div_le_iff₀ hgap).mp hlogN
  have hpoint := coefficient_scale_le_fixedWordStirlingLowerLog
    (q := q) (N := N) (c := c) hq (by simpa [D] using hN)
    (by simpa [gap, D] using hthreshold)
  have hk : 1 ≤ fixedWordQuarterStrands q N := by
    dsimp [fixedWordQuarterStrands]
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 6 * (q + 9))).2
    have : 2 * (6 * (q + 9)) ≤ N := by simpa [D] using hN
    omega
  exact hpoint.trans
    (fixedWordStirlingLowerLog_le_log_certifiedKnotCount inputs hq hk)

/-- The fixed-word leading coefficients approach `2/3` from below.  This
Archimedean choice is all that is needed; no limit theorem for the optimized
logarithmic floor enters. -/
theorem exists_fixedWordLeadingCoefficient_gt {c : ℝ} (hc : c < 2 / 3) :
    ∃ q : ℕ, 2 ≤ q ∧ c < fixedWordLeadingCoefficient q := by
  have hd : 0 < (2 : ℝ) - 3 * c := by nlinarith
  obtain ⟨q, hq⟩ := exists_nat_gt
    (max (2 : ℝ) ((2 + 27 * c) / (2 - 3 * c)))
  have hq2R : (2 : ℝ) < q := (le_max_left _ _).trans_lt hq
  have hq2 : 2 ≤ q := by exact_mod_cast (le_of_lt hq2R)
  have hratio : (2 + 27 * c) / (2 - 3 * c) < (q : ℝ) :=
    (le_max_right _ _).trans_lt hq
  have hmul : 2 + 27 * c < (2 - 3 * c) * (q : ℝ) :=
    by simpa [mul_comm] using (div_lt_iff₀ hd).mp hratio
  refine ⟨q, hq2, ?_⟩
  rw [fixedWordLeadingCoefficient,
    Nat.cast_sub (by omega : 1 ≤ q)]
  have hden : (0 : ℝ) < 6 * (q + 9 : ℕ) := by positivity
  apply (lt_div_iff₀ hden).2
  norm_num only [Nat.cast_add, Nat.cast_ofNat]
  nlinarith

/-- Fully checked `2/3` lower-exponent statement.

For every fixed `c < 2/3`, Lean chooses a sufficiently long *fixed* Garside
word, checks its exact stick budget, applies mathlib Stirling, and performs
all remaining floor/log estimates.  The only assumptions are the typed
external mathematical inputs used elsewhere in the manuscript. -/
theorem eventually_coefficient_lower_bound_fixedWord
    {factor : ℕ} {KnotType : Type} {stickNumber : KnotType → ℕ}
    (inputs : StickAsymptoticExternalInputs KnotType stickNumber factor)
    {c : ℝ} (hc : c < 2 / 3) :
    ∀ᶠ N in atTop,
      c * knotLogScale N ≤
        Real.log (certifiedKnotCount stickNumber N : ℝ) := by
  obtain ⟨q, hq, hcq⟩ := exists_fixedWordLeadingCoefficient_gt hc
  exact eventually_coefficient_lower_bound_of_fixedWord inputs hq hcq

/-- Complete conditional certification of the headline order of growth.

The only hypotheses are the typed external geometry/algebraic and
braid/knot-theory theorem packages.  All asymptotic analysis needed for this
`Theta(N log N)` conclusion is proved in Lean using the conservative
`q=2`, `k=floor(N/132)` subfamily and mathlib's Stirling bound. -/
theorem certifiedKnotCount_log_isTheta
    {factor : ℕ} {KnotType : Type} {stickNumber : KnotType → ℕ}
    (inputs : StickAsymptoticExternalInputs KnotType stickNumber factor)
    (hfactor : 1 ≤ factor) :
    (fun N ↦ Real.log (certifiedKnotCount stickNumber N : ℝ)) =Θ[atTop]
      knotLogScale := by
  let knotLog : ℕ → ℝ :=
    fun N ↦ Real.log (certifiedKnotCount stickNumber N : ℝ)
  have hlowerOrder : knotLogScale =O[atTop] knotLog := by
    apply IsBigO.of_bound 264
    filter_upwards [eventually_one_div_264_scale_le_coarseStirlingLowerLog,
      eventually_ge_atTop 132] with N hcoarse hN
    have hk : 1 ≤ coarseQuarterStrands N := by
      dsimp [coarseQuarterStrands]
      omega
    have hlower := coarseStirlingLowerLog_le_log_certifiedKnotCount inputs hk
    have hscale : 0 ≤ knotLogScale N :=
      mul_nonneg (Nat.cast_nonneg N) (Real.log_natCast_nonneg N)
    have hcountLog : 0 ≤ knotLog N :=
      Real.log_natCast_nonneg (certifiedKnotCount stickNumber N)
    change |knotLogScale N| ≤ 264 * |knotLog N|
    rw [abs_of_nonneg hscale, abs_of_nonneg hcountLog]
    nlinarith
  have hcountToUpper : knotLog =O[atTop] unslicedUpperLog factor := by
    apply IsBigO.of_bound'
    filter_upwards [eventually_ge_atTop (max 5 132)] with N hN
    have hN5 : 5 ≤ N := (le_max_left _ _).trans hN
    have hk : 1 ≤ coarseQuarterStrands N := by
      dsimp [coarseQuarterStrands]
      have : 132 ≤ N := (le_max_right _ _).trans hN
      omega
    have hlogUpper : knotLog N ≤ unslicedUpperLog factor N :=
      Real.log_le_log
        (by exact_mod_cast certifiedKnotCount_coarse_pos inputs hk)
        (certifiedKnotCount_finite_upper inputs hN5)
    change |knotLog N| ≤ |unslicedUpperLog factor N|
    rw [abs_of_nonneg (Real.log_natCast_nonneg (certifiedKnotCount stickNumber N)),
      abs_of_nonneg (unslicedUpperLog_nonneg hfactor (by omega))]
    exact hlogUpper
  have hupperOrder : knotLog =O[atTop] knotLogScale :=
    hcountToUpper.trans (unslicedUpperLog_isBigO factor hfactor)
  exact ⟨hupperOrder, hlowerOrder⟩

/-- The one remaining asymptotic arithmetic lemma, stated only for the
explicit floor/log expression left after Lean has applied the global Stirling
bound.  It contains no knot count and no geometric conclusion.

The equivalence is exactly the manuscript's coefficient calculation:
`optimizedStirlingLowerLog N ~ (2/3) N log N`. -/
structure OptimizedParameterArithmetic where
  stirlingLower_isEquivalent :
    optimizedStirlingLowerLog ~[atTop]
      fun N ↦ (2 / 3 : ℝ) * knotLogScale N

/-- Optional arithmetic interface for the manuscript's sharper explicit
deficit at the logarithmic parameter choice.  Unlike the assumption-free
fixed-word theorem below `2/3`, this records the additional claim that the
loss is `(2/3) N log log N + O(N)`.  It is deliberately a statement only
about the explicit numerical envelope. -/
structure OptimizedDeficitArithmetic where
  exists_errorConstant : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
    (2 / 3 : ℝ) * knotLogScale N -
        (2 / 3 : ℝ) * (N : ℝ) * Real.log (Real.log (N : ℝ)) -
        C * (N : ℝ) ≤ optimizedStirlingLowerLog N

/-- Conditional certificate for the displayed optimized deficit refinement.
Lean composes the arithmetic inequality with the exact typed lower transfer;
the only extra input is `OptimizedDeficitArithmetic`. -/
theorem eventually_optimized_deficit_lower_bound
    {factor : ℕ} {KnotType : Type} {stickNumber : KnotType → ℕ}
    (inputs : StickAsymptoticExternalInputs KnotType stickNumber factor)
    (arithmetic : OptimizedDeficitArithmetic) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      (2 / 3 : ℝ) * knotLogScale N -
          (2 / 3 : ℝ) * (N : ℝ) * Real.log (Real.log (N : ℝ)) -
          C * (N : ℝ) ≤
        Real.log (certifiedKnotCount stickNumber N : ℝ) := by
  obtain ⟨C, hC, hdeficit⟩ := arithmetic.exists_errorConstant
  refine ⟨C, hC, ?_⟩
  filter_upwards [hdeficit, eventually_two_le_optimizedWordLength,
    eventually_one_le_optimizedQuarterStrands] with N hlower hq hk
  exact hlower.trans
    (optimizedStirlingLowerLog_le_log_certifiedKnotCount inputs hq hk)

/-- Quantitative meaning of the manuscript's `(2/3 + o(1))` lower exponent:
every fixed coefficient strictly below `2/3` is eventually a valid lower
bound for the normalized logarithm.  This is one-sided; it does not assert
that the normalized knot-count logarithm converges. -/
theorem eventually_coefficient_lower_bound
    {factor : ℕ} {KnotType : Type} {stickNumber : KnotType → ℕ}
    (inputs : StickAsymptoticExternalInputs KnotType stickNumber factor)
    (arithmetic : OptimizedParameterArithmetic)
    {c : ℝ} (hc : c < 2 / 3) :
    ∀ᶠ N in atTop,
      c * knotLogScale N ≤
        Real.log (certifiedKnotCount stickNumber N : ℝ) := by
  obtain ⟨φ, hφ, hlower⟩ :=
    arithmetic.stirlingLower_isEquivalent.exists_eq_mul
  have hratio : c / (2 / 3 : ℝ) < 1 := (div_lt_one (by norm_num)).2 hc
  have hφlower : ∀ᶠ N in atTop, c / (2 / 3 : ℝ) < φ N :=
    hφ.eventually (Ioi_mem_nhds hratio)
  filter_upwards [eventually_two_le_optimizedWordLength,
    eventually_one_le_optimizedQuarterStrands, hlower, hφlower] with
      N hq hk hlowerEq hφN
  have hscale : 0 ≤ knotLogScale N :=
    mul_nonneg (Nat.cast_nonneg N) (Real.log_natCast_nonneg N)
  have hmul := mul_le_mul_of_nonneg_right (le_of_lt hφN)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3) hscale)
  have hcoeff : c * knotLogScale N ≤ optimizedStirlingLowerLog N := by
    rw [hlowerEq]
    norm_num at hmul ⊢
    nlinarith
  exact hcoeff.trans
    (optimizedStirlingLowerLog_le_log_certifiedKnotCount inputs hq hk)

/-- The certified logarithm has order `Theta(N log N)`.  This is an
`IsTheta` statement (two-sided order of growth), deliberately not an
`IsEquivalent` statement (an asymptotic equivalent). -/
theorem certifiedKnotCount_log_isTheta_of_optimizedArithmetic
    {factor : ℕ} {KnotType : Type} {stickNumber : KnotType → ℕ}
    (inputs : StickAsymptoticExternalInputs KnotType stickNumber factor)
    (hfactor : 1 ≤ factor)
    (arithmetic : OptimizedParameterArithmetic) :
    (fun N ↦ Real.log (certifiedKnotCount stickNumber N : ℝ)) =Θ[atTop]
      knotLogScale := by
  let knotLog : ℕ → ℝ :=
    fun N ↦ Real.log (certifiedKnotCount stickNumber N : ℝ)
  have htarget : Tendsto (fun N ↦ (2 / 3 : ℝ) * knotLogScale N) atTop atTop :=
    knotLogScale_tendsto_atTop.const_mul_atTop (by norm_num)
  have hlowerTop : Tendsto optimizedStirlingLowerLog atTop atTop :=
    arithmetic.stirlingLower_isEquivalent.symm.tendsto_atTop htarget
  have hlowerNonneg : ∀ᶠ N in atTop, 0 ≤ optimizedStirlingLowerLog N :=
    hlowerTop.eventually_ge_atTop 0
  have hlowerToCount : optimizedStirlingLowerLog =O[atTop] knotLog := by
    apply IsBigO.of_bound'
    filter_upwards [eventually_two_le_optimizedWordLength,
      eventually_one_le_optimizedQuarterStrands, hlowerNonneg] with N hq hk hnonneg
    change |optimizedStirlingLowerLog N| ≤ |knotLog N|
    rw [abs_of_nonneg hnonneg,
      abs_of_nonneg (Real.log_natCast_nonneg (certifiedKnotCount stickNumber N))]
    exact optimizedStirlingLowerLog_le_log_certifiedKnotCount inputs hq hk
  have hscaleThetaConst :
      knotLogScale =Θ[atTop] (fun N ↦ (2 / 3 : ℝ) * knotLogScale N) := by
    exact ((isTheta_const_mul_left (by norm_num : (2 / 3 : ℝ) ≠ 0)).2
      isTheta_rfl).symm
  have hscaleToLower : knotLogScale =O[atTop] optimizedStirlingLowerLog :=
    (hscaleThetaConst.trans
      arithmetic.stirlingLower_isEquivalent.isTheta.symm).1
  have hlowerOrder : knotLogScale =O[atTop] knotLog :=
    hscaleToLower.trans hlowerToCount
  have hcountToUpper : knotLog =O[atTop] unslicedUpperLog factor := by
    apply IsBigO.of_bound'
    filter_upwards [eventually_ge_atTop 5,
      eventually_two_le_optimizedWordLength,
      eventually_one_le_optimizedQuarterStrands] with N hN hq hk
    change |knotLog N| ≤ |unslicedUpperLog factor N|
    rw [abs_of_nonneg (Real.log_natCast_nonneg (certifiedKnotCount stickNumber N)),
      abs_of_nonneg (unslicedUpperLog_nonneg hfactor (by omega))]
    exact log_certifiedKnotCount_le_unslicedUpperLog inputs hN hq hk
  have hupperOrder : knotLog =O[atTop] knotLogScale :=
    hcountToUpper.trans (unslicedUpperLog_isBigO factor hfactor)
  exact ⟨hupperOrder, hlowerOrder⟩

end

end StickKnots
