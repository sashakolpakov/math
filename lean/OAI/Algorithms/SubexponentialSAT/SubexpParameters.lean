import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.LayoutParameters
import OAI.Algorithms.SubexponentialSAT.SubexpPackingParameters

namespace OAI.Algorithms

/-!
# Growing parameters for the multi-color construction

All finite bounds retain their constants. The asymptotic estimates are uniform
in any incidence bound `Δ ≤ C*(s+1)^d`, where `C,d` remain explicit arguments.
The integer-power characterization of subpolynomial block growth is proved
without interpreting an unbounded search as advice.
-/

namespace SubexponentialSAT.SubexpParameters

open Filter
open scoped Topology Asymptotics

/-- Number of nonzero elements in the fixed degree-four extension. -/
def sizeQ (p : ℕ) : ℕ := p ^ 4 - 1

/-- Exact integer degree, including the floor. -/
def degreeR (p k Δ : ℕ) : ℕ := sizeQ p / (8 * Δ * k * p)

/-- Size of the complete type block with `s` colors. -/
def blockSize (s p Δ : ℕ) : ℕ := s ^ (sizeQ p * (Δ + 1))

/-- A polynomial of any fixed degree is eventually dominated by `2^n`. -/
theorem polynomial_le_two_pow_eventually (C d : ℕ) :
    ∀ᶠ n : ℕ in atTop, C * (n + 1) ^ d ≤ 2 ^ n := by
  have h := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) d
    (r := 2) (by norm_num)).const_mul_left ((C * 2 ^ d : ℕ) : ℝ)
  have hb := h.bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hb, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hcn0 : (0 : ℝ) ≤ ((C * 2 ^ d : ℕ) : ℝ) * (n : ℝ) ^ d := by positivity
  have ht0 : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg hcn0, abs_of_nonneg ht0, one_mul] at hn
  have hnat : C * 2 ^ d * n ^ d ≤ 2 ^ n := by exact_mod_cast hn
  calc
    C * (n + 1) ^ d ≤ C * (2 * n) ^ d :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ = C * 2 ^ d * n ^ d := by rw [mul_pow]; ring
    _ ≤ 2 ^ n := hnat

/-- The quotient used for the bit capacity tends to infinity. -/
theorem tendsto_div_sixteen : Tendsto (fun s : ℕ => s / 16) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b * 16)] with s hs
  exact (Nat.le_div_iff_mul_le (by norm_num)).2 hs

/-- The slowly growing prime still dominates every fixed polynomial in `s`. -/
theorem polynomial_le_two_pow_div_sixteen_eventually (C d : ℕ) :
    ∀ᶠ s : ℕ in atTop, C * (s + 1) ^ d ≤ 2 ^ (s / 16) := by
  have h := tendsto_div_sixteen.eventually
    (polynomial_le_two_pow_eventually (C * 16 ^ d) d)
  filter_upwards [h] with s hs
  have hsize : s + 1 ≤ 16 * (s / 16 + 1) := by omega
  calc
    C * (s + 1) ^ d ≤ C * (16 * (s / 16 + 1)) ^ d :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize _)
    _ = (C * 16 ^ d) * (s / 16 + 1) ^ d := by rw [mul_pow]; ring
    _ ≤ 2 ^ (s / 16) := hs

/-- A sufficient explicit `Q` threshold for the multi-color Chebyshev test. -/
theorem finite_tail_of_Q_bound {s p k Δ Q : ℕ}
    (hs : 32 ≤ s) (hp : 1 < p) (hk : 0 < k) (hΔ : 0 < Δ)
    (hQ : 64 * s * Δ * (8 * Δ * k * p) ^ 2 ≤ Q) :
    32 ≤ Q / (8 * Δ * k * p) ∧
      16 * Q * Δ * s ≤ (Q / (8 * Δ * k * p)) ^ 2 ∧
      Δ * k * (p - 1) * (Q / (8 * Δ * k * p)) < Q := by
  let a := 8 * Δ * k * p
  let R := Q / a
  have ha8 : 8 ≤ a := LayoutParameters.layoutDenom_ge_eight hp hk hΔ
  have ha0 : 0 < a := by omega
  have hbase : (64 * s * Δ * a) * a ≤ Q := by
    calc
      (64 * s * Δ * a) * a = 64 * s * Δ * (8 * Δ * k * p) ^ 2 := by dsimp [a]; ring
      _ ≤ Q := hQ
  have hRlower : 64 * s * Δ * a ≤ R := (Nat.le_div_iff_mul_le ha0).2 hbase
  have hpos : 1 ≤ s * Δ * a := by
    have : 0 < s * Δ * a := by positivity
    omega
  have hR32 : 32 ≤ R := by nlinarith
  have hRpos : 0 < R := by omega
  have hident : Q % a + a * R = Q := Nat.mod_add_div Q a
  have hrem : Q % a < a := Nat.mod_lt Q ha0
  have haR : a ≤ a * R := by simpa using Nat.mul_le_mul_left a (show 1 ≤ R by omega)
  have hQR : Q ≤ 2 * a * R := by nlinarith
  have hmul : a * R ≤ Q := by omega
  have h32 : 32 * s * Δ * a ≤ R := by nlinarith
  have htail : 16 * Q * Δ * s ≤ R ^ 2 := by
    calc
      16 * Q * Δ * s ≤ 16 * (2 * a * R) * Δ * s := by gcongr
      _ = (32 * s * Δ * a) * R := by ring
      _ ≤ R * R := Nat.mul_le_mul_right R h32
      _ = R ^ 2 := by ring
  have hsmall : Δ * k * (p - 1) < a := by
    have hprod : 0 < Δ * k * p := Nat.mul_pos (Nat.mul_pos hΔ hk) (by omega)
    calc
      Δ * k * (p - 1) ≤ Δ * k * p := Nat.mul_le_mul_left _ (Nat.sub_le p 1)
      _ < 8 * (Δ * k * p) := by omega
      _ = a := by dsimp [a]; ring
  exact ⟨hR32, htail, lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hsmall hRpos) hmul⟩

/-- The fixed extension degree four is enough under an explicit prime-size test. -/
theorem quartic_feasible {s p k Δ : ℕ}
    (hs : 32 ≤ s) (hp : 1 < p) (hk : 0 < k) (hΔ : 0 < Δ)
    (hprime : 8192 * s * Δ ^ 3 * k ^ 2 ≤ p ^ 2) :
    32 ≤ degreeR p k Δ ∧
      16 * sizeQ p * Δ * s ≤ (degreeR p k Δ) ^ 2 ∧
      Δ * k * (p - 1) * degreeR p k Δ < sizeQ p := by
  apply finite_tail_of_Q_bound hs hp hk hΔ
  let b := 4096 * s * Δ ^ 3 * k ^ 2
  have hb : 1 ≤ b := by
    have : 0 < b := by dsimp [b]; positivity
    omega
  have htwob : 2 * b ≤ p ^ 2 := by dsimp [b]; nlinarith [hprime]
  have hbp : b + 1 ≤ p ^ 2 := by omega
  have hprod := Nat.mul_le_mul_right (p ^ 2) hbp
  have hp2 : 1 ≤ p ^ 2 := by
    have : 0 < p ^ 2 := by positivity
    omega
  have hstrict : b * p ^ 2 + 1 ≤ p ^ 4 := by nlinarith [hprod]
  have hresult : b * p ^ 2 ≤ p ^ 4 - 1 := by omega
  calc
    64 * s * Δ * (8 * Δ * k * p) ^ 2 = b * p ^ 2 := by dsimp [b]; ring
    _ ≤ sizeQ p := hresult


/-- The quartic extension size has a precise dyadic upper bound. -/
lemma sizeQ_le_dyadic {s p : ℕ} (hp : p ≤ 2 ^ (s / 16 + 1)) :
    sizeQ p ≤ 16 * 2 ^ (4 * (s / 16)) := by
  calc
    sizeQ p ≤ p ^ 4 := Nat.sub_le _ _
    _ ≤ (2 ^ (s / 16 + 1)) ^ 4 := Nat.pow_le_pow_left hp _
    _ = 2 ^ ((s / 16 + 1) * 4) := by rw [pow_mul]
    _ = 2 ^ (4 + 4 * (s / 16)) := by congr 1; omega
    _ = 16 * 2 ^ (4 * (s / 16)) := by rw [pow_add]; norm_num

/-- A finite inequality sufficient for every requested fixed power of the block
size to fit below the natural double-exponential scale. -/
theorem blockSize_pow_le_doubleExp {s p Δ t : ℕ}
    (hp : p ≤ 2 ^ (s / 16 + 1))
    (hbudget : 16 * t * s * (Δ + 1) ≤ 2 ^ (s / 16)) :
    (blockSize s p Δ) ^ t ≤ 2 ^ (2 ^ s) := by
  have hs : s ≤ 2 ^ s := Nat.le_of_lt (Nat.lt_pow_self (by norm_num : 1 < 2))
  have hQ := sizeQ_le_dyadic hp
  have hexp : s * (sizeQ p * (Δ + 1) * t) ≤ 2 ^ s := by
    calc
      s * (sizeQ p * (Δ + 1) * t) ≤
          s * ((16 * 2 ^ (4 * (s / 16))) * (Δ + 1) * t) := by gcongr
      _ = (16 * t * s * (Δ + 1)) * 2 ^ (4 * (s / 16)) := by ring
      _ ≤ 2 ^ (s / 16) * 2 ^ (4 * (s / 16)) := Nat.mul_le_mul_right _ hbudget
      _ = 2 ^ (5 * (s / 16)) := by rw [← pow_add]; congr 1; omega
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold blockSize
  rw [← pow_mul]
  calc
    s ^ (sizeQ p * (Δ + 1) * t) ≤ (2 ^ s) ^ (sizeQ p * (Δ + 1) * t) :=
      Nat.pow_le_pow_left hs _
    _ = 2 ^ (s * (sizeQ p * (Δ + 1) * t)) := by simp only [← pow_mul, Nat.mul_assoc]
    _ ≤ 2 ^ (2 ^ s) := Nat.pow_le_pow_right (by norm_num) hexp

/-- Uniform subpolynomial growth on the logarithmic scale. Constants and the
incidence polynomial degree remain explicit. -/
theorem blockSize_subpolynomial_in_s (C d t : ℕ) :
    ∀ᶠ s : ℕ in atTop, ∀ p Δ : ℕ,
      Δ ≤ C * (s + 1) ^ d → p ≤ 2 ^ (s / 16 + 1) →
        (blockSize s p Δ) ^ t ≤ 2 ^ (2 ^ s) := by
  have h := polynomial_le_two_pow_div_sixteen_eventually (16 * t * (C + 1)) (d + 1)
  filter_upwards [h] with s hs p Δ hΔ hp
  apply blockSize_pow_le_doubleExp hp
  have hone : 1 ≤ (s + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have hΔ' : Δ + 1 ≤ (C + 1) * (s + 1) ^ d := by nlinarith
  calc
    16 * t * s * (Δ + 1) ≤ 16 * t * (s + 1) * ((C + 1) * (s + 1) ^ d) := by gcongr; omega
    _ = (16 * t * (C + 1)) * (s + 1) ^ (d + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ (s / 16) := hs

/-- Concrete `N = n^{o(1)}` statement for the actual computable input schedule:
every fixed natural power of the block size is eventually at most `n`. -/
theorem blockSize_subpolynomial (C d t : ℕ) (δ : ℕ → ℕ)
    (hδ : ∀ᶠ n : ℕ in atTop,
      δ n ≤ C * (SubexpPackingParameters.s n + 1) ^ d) :
    ∀ᶠ n : ℕ in atTop,
      (blockSize (SubexpPackingParameters.s n) (SubexpPackingParameters.p n) (δ n)) ^ t ≤ n := by
  have h := SubexpPackingParameters.tendsto_s_atTop.eventually
    (blockSize_subpolynomial_in_s C d t)
  filter_upwards [h, hδ, SubexpPackingParameters.eventually_goodInput] with n hn hδn hgood
  have hp : SubexpPackingParameters.p n ≤ 2 ^ (SubexpPackingParameters.s n / 16 + 1) :=
    le_of_lt (SubexpPackingParameters.p_upper hgood)
  exact (hn _ _ hδn hp).trans
    (SubexpPackingParameters.pow_pow_s_le (SubexpPackingParameters.goodInput_two_le hgood))


/-- The exact threshold appearing in the full-block packing condition. -/
def blockThreshold (s p k Δ : ℕ) : ℕ :=
  s ^ 2 * (blockSize s p Δ) ^ 3 * (1 + Δ * k)

lemma polynomial_factor_le_power {s C e : ℕ} (hs : 2 ≤ s) (hC : C ≤ s) :
    C * (s + 1) ^ e ≤ s ^ (2 * e + 1) := by
  have hsquare : s + 1 ≤ s ^ 2 := by nlinarith
  calc
    C * (s + 1) ^ e ≤ s * (s ^ 2) ^ e := by gcongr
    _ = s ^ (2 * e + 1) := by rw [pow_add, pow_one, pow_mul]; ring

lemma base_le_blockSize {s p Δ : ℕ} (hs : 1 ≤ s) (hp : 2 ≤ p) :
    s ≤ blockSize s p Δ := by
  have hpow : 16 ≤ p ^ 4 := by simpa using Nat.pow_le_pow_left hp 4
  have hQ : 0 < sizeQ p := by unfold sizeQ; omega
  have he : 1 ≤ sizeQ p * (Δ + 1) := by
    have : 0 < sizeQ p * (Δ + 1) := Nat.mul_pos hQ (by omega)
    omega
  calc
    s = s ^ 1 := by simp
    _ ≤ s ^ (sizeQ p * (Δ + 1)) := Nat.pow_le_pow_right hs he
    _ = blockSize s p Δ := rfl

/-- A finite reduction of the packing threshold, including the chunk length,
to one fixed power of the universal block size. -/
theorem blockThreshold_mul_ell_le_power {s p k Δ C d ell : ℕ}
    (hs : 2 ≤ s) (hp : 2 ≤ p) (hC : 1 + C * k ≤ s)
    (hΔ : Δ ≤ C * (s + 1) ^ d) (hell : ell ≤ s) :
    blockThreshold s p k Δ * ell ≤ (blockSize s p Δ) ^ (2 * d + 10) := by
  let N := blockSize s p Δ
  have hsN : s ≤ N := base_le_blockSize (by omega) hp
  have hone : 1 ≤ (s + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have hΔk := Nat.mul_le_mul_right k hΔ
  have hfactor : 1 + Δ * k ≤ (1 + C * k) * (s + 1) ^ d := by nlinarith
  have hpoly := polynomial_factor_le_power (e := d + 3) hs hC
  calc
    blockThreshold s p k Δ * ell = s ^ 2 * N ^ 3 * (1 + Δ * k) * ell := rfl
    _ ≤ (s + 1) ^ 2 * N ^ 3 * ((1 + C * k) * (s + 1) ^ d) * (s + 1) := by
      gcongr <;> omega
    _ = (1 + C * k) * (s + 1) ^ (d + 3) * N ^ 3 := by rw [pow_add]; ring
    _ ≤ s ^ (2 * (d + 3) + 1) * N ^ 3 := Nat.mul_le_mul_right _ hpoly
    _ ≤ N ^ (2 * (d + 3) + 1) * N ^ 3 := by gcongr
    _ = N ^ (2 * d + 10) := by rw [← pow_add]; congr 1

/-- The block-packing test succeeds eventually for the actual schedule, for
every fixed polynomial incidence bound. -/
theorem blockThreshold_eventually_le_D (C d k : ℕ) (δ : ℕ → ℕ)
    (hδ : ∀ᶠ n : ℕ in atTop,
      δ n ≤ C * (SubexpPackingParameters.s n + 1) ^ d) :
    ∀ᶠ n : ℕ in atTop,
      blockThreshold (SubexpPackingParameters.s n) (SubexpPackingParameters.p n) k (δ n) ≤
        SubexpPackingParameters.D n := by
  have hN := blockSize_subpolynomial C d (2 * d + 10) δ hδ
  have hs := SubexpPackingParameters.tendsto_s_atTop.eventually
    (eventually_ge_atTop (max 2 (1 + C * k)))
  filter_upwards [hN, hδ, hs, SubexpPackingParameters.eventually_goodInput] with n hNn hδn hsn hgood
  have hsp : 2 ≤ SubexpPackingParameters.s n := le_trans (le_max_left _ _) hsn
  have hCp : 1 + C * k ≤ SubexpPackingParameters.s n := le_trans (le_max_right _ _) hsn
  have hp : 2 ≤ SubexpPackingParameters.p n := le_of_lt (SubexpPackingParameters.p_gt_two n)
  have hell : SubexpPackingParameters.ell n ≤ SubexpPackingParameters.s n :=
    SubexpPackingParameters.u_le_s n
  have hfinite := blockThreshold_mul_ell_le_power hsp hp hCp hδn hell
  have htotal := (hfinite.trans hNn).trans (SubexpPackingParameters.n_le_D_mul_ell hgood)
  exact Nat.le_of_mul_le_mul_right htotal (SubexpPackingParameters.ell_pos hgood)


/-- The degree choice leaves enough room on both sides of every binomial mean. -/
theorem four_mul_degreeR_le_Q {p k Δ : ℕ}
    (hp : 1 < p) (hk : 0 < k) (hΔ : 0 < Δ) :
    4 * degreeR p k Δ ≤ sizeQ p := by
  have ha := LayoutParameters.layoutDenom_ge_eight hp hk hΔ
  change 8 ≤ 8 * Δ * k * p at ha
  calc
    4 * degreeR p k Δ ≤ (8 * Δ * k * p) * degreeR p k Δ :=
      Nat.mul_le_mul_right _ (by omega)
    _ ≤ sizeQ p := Nat.mul_div_le _ _

end SubexponentialSAT.SubexpParameters

end OAI.Algorithms
