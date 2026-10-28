import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticResidualLayout

namespace OAI.Algorithms

/-! The raw-matrix label base may use the ambient number of Boolean
coordinates. The factor-two envelope below is proof-only; the produced
occurrence, radius and polynomial cutoff remain the actual values. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly
open Filter
open scoped Topology
open Asymptotic

theorem eventually_ambient_label_log (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m B : ℕ, n ≤ 2*m → 0 < B → B ≤ L m^q →
      Real.log (4*(n:ℝ)*B*(8*(layoutQ m:ℝ))^(2*layoutCutoff m B)+1)
        ≤ 4*(L m:ℝ)^2 := by
  filter_upwards [eventually_uniform_half (eventually_uniform_label_log (q+1)),
    eventually_uniform_half (eventually_L_ge 2),
    eventually_uniform_half (eventually_layoutQ_ge 1)] with n hn hL hQ m B hnm hB hb
  have h2 : 2*B ≤ L m^(q+1) := by
    calc
      2*B ≤ L m*L m^q := Nat.mul_le_mul (hL m hnm) hb
      _ = L m^(q+1) := by rw [pow_succ]; ring_nf
  have h := hn m hnm (2*B) (by omega) h2
  have hc := layoutCutoff_mono m (show B ≤ 2*B by omega)
  have hnp : (n:ℝ) ≤ 2*m := by exact_mod_cast hnm
  have hqp : (1:ℝ) ≤ 8*(layoutQ m:ℝ) := by
    have : (1:ℝ) ≤ layoutQ m := by exact_mod_cast hQ m hnm
    linarith
  have harg : 4*(n:ℝ)*B*(8*(layoutQ m:ℝ))^(2*layoutCutoff m B)+1 ≤
      4*(m:ℝ)*(2*B)*(8*(layoutQ m:ℝ))^(2*layoutCutoff m (2*B))+1 := by
    calc
      _ ≤ 4*(2*(m:ℝ))*B*(8*(layoutQ m:ℝ))^(2*layoutCutoff m (2*B))+1 := by
        gcongr
      _ = _ := by ring_nf
  have hp : 0 < 4*(n:ℝ)*B*(8*(layoutQ m:ℝ))^(2*layoutCutoff m B)+1 := by positivity
  exact (Real.log_le_log hp harg).trans (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using h)

/-- Exactly the common base 2*ambient*height+1 for height
2*B*(8Q)^(2R), without changing any executed parameter. -/
theorem eventually_ambient_commonBase_log (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m B : ℕ, n ≤ 2*m → 0 < B → B ≤ L m^q →
      Real.log ((2*n*(2*B*(8*layoutQ m)^(2*layoutCutoff m B))+1:ℕ):ℝ)
        ≤ 4*(L m:ℝ)^2 := by
  filter_upwards [eventually_ambient_label_log q] with n hn m B hnm hB hb
  convert hn m B hnm hB hb using 1
  push_cast
  ring_nf

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
