import StickKnots.AsymptoticCertificate

/-!
# Internal arithmetic of the manuscript's refined bounds

The geometric and knot-theoretic inputs remain those of
`StickAsymptoticExternalInputs`.  This module discharges the additional
floor/log arithmetic in the manuscript, including its explicit second-order
lower deficit, and extracts the leading upper coefficient `3`.
-/

namespace StickKnots

open Filter Function Asymptotics

noncomputable section

/-- The finite upper logarithm has leading coefficient three and a linear
error.  No asymptotic estimate is supplied as a hypothesis. -/
theorem unslicedUpperLog_le_three_scale_add_linear
    {factor N : ℕ} (hf : 1 ≤ factor) (hN : 1 ≤ N) :
    unslicedUpperLog factor N ≤ 3 * knotLogScale N +
      (3 * Real.log (12 * (factor : ℝ)) + 4) * (N : ℝ) := by
  have hx : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hfpos : (0 : ℝ) < factor := by exact_mod_cast (show 0 < factor by omega)
  have hfirst : Real.log (3 * (N : ℝ) + 1) ≤ 4 * (N : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 3 * N + 1)
    nlinarith
  unfold unslicedUpperLog knotLogScale
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    show (12 * (factor : ℝ) * N) = (12 * (factor : ℝ)) * (N : ℝ) by ring,
    Real.log_mul (by positivity) (ne_of_gt hx)]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

/-- Every coefficient above three is an eventual upper bound for the
normalized knot-count logarithm. -/
theorem eventually_coefficient_upper_bound
    {factor : ℕ} {KnotType : Type} {stickNumber : KnotType → ℕ}
    (inputs : StickAsymptoticExternalInputs KnotType stickNumber factor)
    (hf : 1 ≤ factor) {c : ℝ} (hc : 3 < c) :
    ∀ᶠ N in atTop,
      Real.log (certifiedKnotCount stickNumber N : ℝ) ≤ c * knotLogScale N := by
  let E : ℝ := 3 * Real.log (12 * (factor : ℝ)) + 4
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (E / (c - 3))
  filter_upwards [hlog, eventually_ge_atTop 132] with N hL hN
  have hk : 1 ≤ coarseQuarterStrands N := by
    dsimp [coarseQuarterStrands]
    omega
  have hcount := certifiedKnotCount_coarse_pos inputs hk
  have hupper := Real.log_le_log (by exact_mod_cast hcount)
    (certifiedKnotCount_finite_upper inputs (by omega : 5 ≤ N))
  have hE : E ≤ (c - 3) * Real.log (N : ℝ) := by
    simpa [mul_comm] using (div_le_iff₀ (by linarith : 0 < c - 3)).mp hL
  have hEN := mul_le_mul_of_nonneg_right hE (Nat.cast_nonneg N)
  have hlinear := unslicedUpperLog_le_three_scale_add_linear hf (by omega : 1 ≤ N)
  change Real.log (certifiedKnotCount stickNumber N : ℝ) ≤ unslicedUpperLog factor N
    at hupper
  dsimp [E, knotLogScale] at hEN hlinear ⊢
  nlinarith

set_option maxHeartbeats 2000000 in
/-- A pointwise version of the optimized deficit.  The three size conditions
hold eventually and are discharged below using mathlib's logarithm limits. -/
theorem optimizedStirlingLowerLog_deficit_of_size
    {N : ℕ} (hN : 15 ≤ N) (hL : 2 ≤ Real.log (N : ℝ))
    (hLsq : Real.log (N : ℝ) ^ 2 ≤ (N : ℝ))
    (hden : 12 * (optimizedWordLength N + 9) ≤ N) :
    (2 / 3 : ℝ) * knotLogScale N -
        (2 / 3 : ℝ) * (N : ℝ) * Real.log (Real.log (N : ℝ)) -
        100 * (N : ℝ) ≤ optimizedStirlingLowerLog N := by
  let q := optimizedWordLength N
  let k := optimizedQuarterStrands N
  let x : ℝ := N
  let L : ℝ := Real.log x
  let n : ℝ := 4 * (k : ℝ)
  let M : ℝ := ((q - 1 : ℕ) : ℝ) * n
  change 2 ≤ L at hL
  change L ^ 2 ≤ x at hLsq
  have hx : 15 ≤ x := by dsimp [x]; exact_mod_cast hN
  have hq : 2 ≤ q := by
    exact (Nat.le_floor_iff (by linarith : 0 ≤ Real.log (N : ℝ))).mpr hL
  have hqle : (q : ℝ) ≤ L := Nat.floor_le (by change 0 ≤ L; linarith)
  have hqsub : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    norm_num
  have hk : 1 ≤ k := by
    dsimp [k, optimizedQuarterStrands]
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 12 * (q + 9))).2
    dsimp [q] at hden ⊢
    omega
  have hcap := optimizedQuarterStrands_capacity N
  have hrem : 2 * N + 15 < 12 * (q + 9) * (k + 1) := by
    have h := Nat.mod_lt (2 * N + 15) (by omega : 0 < 12 * (q + 9))
    have heq := Nat.div_add_mod (2 * N + 15) (12 * (q + 9))
    change 12 * (q + 9) * k + (2 * N + 15) % (12 * (q + 9)) = 2 * N + 15
      at heq
    nlinarith
  have hcapR : 3 * n * ((q : ℝ) + 9) ≤ 2 * x + 15 := by
    have hh : (3 : ℝ) * ((4 * (optimizedQuarterStrands N : ℝ)) *
        ((optimizedWordLength N : ℝ) + 9)) ≤ 2 * (N : ℝ) + 15 := by
      exact_mod_cast hcap
    simpa [n, k, q, x, mul_assoc] using hh
  have hremR : 2 * x + 15 < 3 * n * ((q : ℝ) + 9) + 12 * ((q : ℝ) + 9) := by
    have := (show (2 * N + 15 : ℝ) < 12 * (q + 9 : ℝ) * (k + 1 : ℝ) by
      exact_mod_cast hrem)
    dsimp [x, n]
    nlinarith
  have hnpos : 0 < n := by dsimp [n]; positivity
  have hnq : n * ((q : ℝ) + 9) ≤ x := by nlinarith
  have hML : 0 ≤ M := by dsimp [M, n]; positivity
  have hMcap : M ≤ (2 / 3 : ℝ) * x + 5 := by
    dsimp [M]
    rw [hqsub]
    nlinarith
  have hMx : M ≤ x := by nlinarith
  have hq9 : (q : ℝ) + 9 ≤ 10 * L := by dsimp [L, x] at *; linarith
  have hnL : n * L ≤ x := by
    have hfloor : L < (q : ℝ) + 1 := Nat.lt_floor_add_one L
    nlinarith
  have hfloorLoss := mul_le_mul_of_nonneg_right (le_of_lt hremR) (by linarith : 0 ≤ L)
  have hqLoss := mul_le_mul_of_nonneg_right hq9 (by linarith : 0 ≤ L)
  have hlead : (2 / 3 : ℝ) * x * L - 50 * x ≤ M * L := by
    have hMeq : M * L = n * ((q : ℝ) + 9) * L - 10 * (n * L) := by
      dsimp [M]
      rw [hqsub]
      ring
    nlinarith
  have hxnk : (N : ℝ) ≤ 12 * ((q : ℝ) + 9) * (k : ℝ) := by
    have hd : (12 * (q + 9) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hden
    dsimp [x, n] at hremR
    nlinarith
  have hroute : x ≤ 30 * L * n := by
    have h := mul_le_mul_of_nonneg_right hq9 (le_of_lt hnpos)
    dsimp [x, n] at *
    nlinarith
  have hlogRoute := Real.log_le_log (by dsimp [x]; positivity) hroute
  rw [Real.log_mul (by positivity : (30 * L : ℝ) ≠ 0) (ne_of_gt hnpos),
    Real.log_mul (by norm_num : (30 : ℝ) ≠ 0) (by linarith : L ≠ 0)] at hlogRoute
  have hlogn : L - Real.log L - Real.log 30 ≤ Real.log n := by
    change Real.log x ≤ _ at hlogRoute
    dsimp [L] at *
    linarith
  have hlogLnonneg : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hlogLx : Real.log L ≤ x := by
    have h := Real.log_le_sub_one_of_pos (by linarith : 0 < L)
    nlinarith [sq_nonneg (L - 1)]
  have hlog30 : Real.log 30 ≤ 29 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 30)
    norm_num at this ⊢
    linarith
  have hlog30nonneg : 0 ≤ Real.log 30 := Real.log_nonneg (by norm_num)
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    linarith
  have hlog2nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hmain := mul_le_mul_of_nonneg_left hlogn hML
  have hsublog := mul_le_mul_of_nonneg_right hMcap hlogLnonneg
  have hconst := mul_le_mul_of_nonneg_right hMx hlog30nonneg
  have hconst' := mul_le_mul_of_nonneg_left hlog30 (by linarith : 0 ≤ x)
  have hqk : (q : ℝ) * k ≤ x := by dsimp [n] at hnq; nlinarith
  have herror := mul_le_mul_of_nonneg_right hqk hlog2nonneg
  have herror' := mul_le_mul_of_nonneg_left hlog2 (by linarith : 0 ≤ x)
  have henvelope : optimizedStirlingLowerLog N =
      M * Real.log n - M - 9 * (q : ℝ) * k * Real.log 2 - Real.log 2 := by
    dsimp [optimizedStirlingLowerLog, M, n, q, k]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [henvelope]
  change (2 / 3 : ℝ) * (x * L) - (2 / 3 : ℝ) * x * Real.log L - 100 * x ≤ _
  nlinarith

/-- The manuscript's optimized arithmetic interface is inhabited by a Lean
proof.  The constant 100 is deliberately loose; the manuscript needs `O(N)`. -/
theorem provedOptimizedDeficitArithmetic : OptimizedDeficitArithmetic := by
  have hsqLittle : (fun N : ℕ ↦ Real.log (N : ℝ) ^ 2) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) :=
    Real.isLittleO_pow_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have hsq := (isLittleO_iff_nat_mul_le.mp hsqLittle) 1
  have hsmall : (fun N : ℕ ↦ Real.log (N : ℝ)) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have hlogBound := (isLittleO_iff_nat_mul_le.mp hsmall) 24
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  refine ⟨100, by norm_num, ?_⟩
  filter_upwards [hsq, hlogBound, hlog, eventually_ge_atTop 216] with
    N hs hb hL hN
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg N)] at hs
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg N),
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg N)] at hb
  have hq := Nat.floor_le (Real.log_natCast_nonneg N)
  have hden : 12 * (optimizedWordLength N + 9) ≤ N := by
    have hNr : (216 : ℝ) ≤ N := by exact_mod_cast hN
    have : (12 : ℝ) * ((optimizedWordLength N : ℝ) + 9) ≤ N := by
      change (optimizedWordLength N : ℝ) ≤ Real.log (N : ℝ) at hq
      norm_num at hb
      nlinarith
    exact_mod_cast this
  exact optimizedStirlingLowerLog_deficit_of_size (by omega) hL (by simpa using hs) hden

/-- The displayed second-order deficit now needs only the cited external
geometry, real algebraic geometry, braid theory and knot theory inputs. -/
theorem eventually_optimized_deficit_lower_bound_proved
    {factor : ℕ} {KnotType : Type} {stickNumber : KnotType → ℕ}
    (inputs : StickAsymptoticExternalInputs KnotType stickNumber factor) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      (2 / 3 : ℝ) * knotLogScale N -
          (2 / 3 : ℝ) * (N : ℝ) * Real.log (Real.log (N : ℝ)) -
          C * (N : ℝ) ≤ Real.log (certifiedKnotCount stickNumber N : ℝ) :=
  eventually_optimized_deficit_lower_bound inputs provedOptimizedDeficitArithmetic

end

end StickKnots
