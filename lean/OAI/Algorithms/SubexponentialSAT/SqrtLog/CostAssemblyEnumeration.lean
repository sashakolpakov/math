import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticLayoutCost

namespace OAI.Algorithms

/-! The integer-signature and head-bucket enumeration costs, with the actual
joint-signature count rather than rank used as the exponential resource. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open Asymptotic

/-- Uniform head size and joint-label estimates give this concrete enumeration
counter.  The number of heads is a polynomial factor, not an exponent n. -/
def enumerationWork (labelBase rows heads headSize : ℕ) : ℕ :=
  labelBase^rows * heads * 2^headSize

/-- Natural integer signature range, converted to the exact binary exponent. -/
theorem enumerationWork_le (labelBase rows heads headSize : ℕ)
    (hbase : 0 < labelBase) {e f g : ℝ}
    (he : (rows:ℝ)*Real.logb 2 labelBase ≤ e)
    (hf : (headSize:ℝ) ≤ f)
    (hg : (heads:ℝ) ≤ (2:ℝ)^g) :
    (enumerationWork labelBase rows heads headSize:ℝ) ≤ (2:ℝ)^(e+g+f) := by
  have hb : (0:ℝ) < labelBase := by exact_mod_cast hbase
  have hlabel : ((labelBase^rows:ℕ):ℝ) ≤ (2:ℝ)^e := by
    calc
      _ = (2:ℝ)^((rows:ℝ)*Real.logb 2 labelBase) := by
        push_cast
        rw [mul_comm, Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast,
          Real.rpow_logb (by norm_num) (by norm_num) hb]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) he
  have hhead : ((2^headSize:ℕ):ℝ) ≤ (2:ℝ)^f := by
    push_cast
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hf
  push_cast at hlabel hhead
  unfold enumerationWork
  push_cast
  calc
    _ ≤ (2:ℝ)^e*(2:ℝ)^g*(2:ℝ)^f := by
      exact mul_le_mul (mul_le_mul hlabel hg (by positivity) (by positivity))
        hhead (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]

/-- With epsilon=1/(32 B r L²), total rows ≤ 2 epsilon n B means
16 r L² rows ≤ n.  Combined with the integer label-height bound, the logarithm
of the full joint signature image is at most n/(2r). -/
theorem signature_log_budget (base rows : ℕ) {n r l : ℝ}
    (hr : 0 < r) (hrows : 16*r*l^2*(rows:ℝ) ≤ n)
    (hheight : Real.log (base:ℝ) ≤ 4*l^2) :
    (rows:ℝ)*Real.logb 2 base ≤ n/(2*r) := by
  have h2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2 := log_two_bounds
  have hheight' := mul_le_mul_of_nonneg_left hheight (show (0:ℝ) ≤ rows by positivity)
  have hh : (rows:ℝ)*Real.log (base:ℝ)/Real.log 2 ≤ 8*(rows:ℝ)*l^2 := by
    apply (div_le_iff₀ h2p).2
    have hs : 0 ≤ (rows:ℝ)*l^2 := by positivity
    nlinarith
  unfold Real.logb
  rw [← mul_div_assoc]
  apply hh.trans
  apply (le_div_iff₀ (by positivity : (0:ℝ) < 2*r)).2
  nlinarith

/-- Both the label enumeration and the head assignments fit the target.
The concrete head estimate 3n/(2r) is relaxed to 2n/r, and heads ≤ n+1 is
charged through a logarithmic exponent. -/
theorem eventually_enumeration_target
    (base rows heads headSize : ℕ → ℕ)
    (hbase : ∀ᶠ n:ℕ in atTop, 0 < base n)
    (hrows : ∀ᶠ n:ℕ in atTop,
      16*(layoutR n:ℝ)*(L n:ℝ)^2*(rows n:ℝ) ≤ n)
    (hheight : ∀ᶠ n:ℕ in atTop, Real.log (base n:ℝ) ≤ 4*(L n:ℝ)^2)
    (hheads : ∀ᶠ n:ℕ in atTop, heads n ≤ n+1)
    (hsize : ∀ᶠ n:ℕ in atTop, (headSize n:ℝ) ≤ 2*(n:ℝ)/layoutR n) :
    ∀ᶠ n:ℕ in atTop,
      (enumerationWork (base n) (rows n) (heads n) (headSize n):ℝ) ≤
      (2:ℝ)^(321*Statement.runtimeScale n) := by
  have hpoly := eventually_polylog_le_target 1 (by norm_num : (0:ℝ) < 1)
  filter_upwards [hbase,hrows,hheight,hheads,hsize,
    eventually_layout_inverse_target,hpoly] with n hb hr hh hd hs hi hp
  have hrpos : (0:ℝ) < layoutR n := by
    have := layoutR_ge_two n
    exact_mod_cast (by omega : 0 < layoutR n)
  have he := signature_log_budget (base n) (rows n) hrpos hr hh
  have hE : (rows n:ℝ)*Real.logb 2 (base n) ≤ 64*Statement.runtimeScale n := by
    have : (n:ℝ)/(2*layoutR n) = ((n:ℝ)/layoutR n)/2 := by ring
    rw [this] at he
    linarith
  have hF : (headSize n:ℝ) ≤ 256*Statement.runtimeScale n := by
    have : 2*(n:ℝ)/layoutR n = 2*((n:ℝ)/layoutR n) := by ring
    rw [this] at hs
    linarith
  have hG : (heads n:ℝ) ≤ (2:ℝ)^Statement.runtimeScale n := by
    have hlog : logSize n ≤ Statement.runtimeScale n := by simpa using hp
    calc
      _ ≤ (n:ℝ)+1 := by exact_mod_cast hd
      _ ≤ (n:ℝ)+16 := by linarith
      _ = (2:ℝ)^logSize n := by
        symm
        exact Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hlog
  convert enumerationWork_le (base n) (rows n) (heads n) (headSize n) hb hE hF hG using 1
  congr 1
  ring

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
