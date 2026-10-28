import OAI.Analysis.PDE.Variational.CellL2
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open Set Filter _root_.MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Variational

def zeroValueBump : ContDiffBump (0 : ℝ) := ⟨1,2,by norm_num,by norm_num⟩

def valueCutoff (c t : ℝ) : ℝ := (1-zeroValueBump (c*t))*t

def valueCutoffSlope (s : ℝ) : ℝ := 1-zeroValueBump s-s*deriv zeroValueBump s

theorem valueCutoff_zero (c : ℝ) : valueCutoff c 0=0 := by simp [valueCutoff]

theorem contDiff_valueCutoff (c : ℝ) : ContDiff ℝ ∞ (valueCutoff c) :=
  (contDiff_const.sub (zeroValueBump.contDiff.comp (contDiff_const.mul contDiff_id))).mul contDiff_id

theorem hasDerivAt_valueCutoff (c t : ℝ) :
    HasDerivAt (valueCutoff c) (valueCutoffSlope (c*t)) t := by
  have hb := ((zeroValueBump.contDiff : ContDiff ℝ 1 (zeroValueBump : ℝ→ℝ)).differentiable one_ne_zero (c*t)).hasDerivAt
  convert ((hasDerivAt_const t (1:ℝ)).sub (hb.comp t ((hasDerivAt_id t).const_mul c))).mul
    (hasDerivAt_id t) using 1 <;>
    (try funext x) <;>
    (try simp only [valueCutoff, valueCutoffSlope, Pi.sub_apply, Pi.mul_apply, Function.comp_apply, id_eq]) ; ring

theorem abs_valueCutoff_le (c t : ℝ) : |valueCutoff c t|≤|t| := by
  rw [valueCutoff,abs_mul,abs_of_nonneg (sub_nonneg.mpr zeroValueBump.le_one)]
  exact mul_le_of_le_one_left (abs_nonneg _) (by linarith [zeroValueBump.nonneg (x:=c*t)])

theorem valueCutoff_eq_zero_of_small (c t : ℝ) (h : |c*t|≤1) : valueCutoff c t=0 := by
  have hb : zeroValueBump (c*t)=1 := zeroValueBump.one_of_mem_closedBall (by
    simpa [zeroValueBump,mem_closedBall,Real.dist_eq] using h)
  simp [valueCutoff,hb]

theorem zeroValueBump_deriv_zero {s : ℝ} (hs : 2 < |s|) : deriv zeroValueBump s=0 := by
  apply deriv_of_notMem_tsupport
  rw [zeroValueBump.tsupport_eq]
  simpa [zeroValueBump,mem_closedBall,Real.dist_eq] using not_le.mpr hs

theorem valueCutoff_eq_self_of_large (c t : ℝ) (h : 2≤|c*t|) : valueCutoff c t=t := by
  have hb : zeroValueBump (c*t)=0 := zeroValueBump.zero_of_le_dist (by
    simpa [zeroValueBump,Real.dist_eq] using h)
  simp [valueCutoff,hb]

theorem valueCutoffSlope_eq_one_of_large {s : ℝ} (hs : 2 < |s|) : valueCutoffSlope s=1 := by
  have hb : zeroValueBump s=0 := zeroValueBump.zero_of_le_dist (by
    simpa [zeroValueBump,Real.dist_eq] using hs.le)
  simp [valueCutoffSlope,hb,zeroValueBump_deriv_zero hs]

theorem valueCutoffSlope_bounded : ∃C:ℝ, 0≤C ∧ ∀s, |valueCutoffSlope s|≤C := by
  have hc : Continuous (deriv zeroValueBump) :=
    (zeroValueBump.contDiff : ContDiff ℝ 1 (zeroValueBump : ℝ→ℝ)).continuous_deriv le_rfl
  obtain ⟨D,hD⟩ := (zeroValueBump.hasCompactSupport.deriv.isCompact_range hc).isBounded.exists_norm_le
  have hD0 : 0≤D := (norm_nonneg _).trans (hD _ (mem_range_self 0))
  refine ⟨2+2*D,by positivity,fun s ↦ ?_⟩
  by_cases hs : 2 < |s|
  · rw [valueCutoffSlope_eq_one_of_large hs,abs_one]
    linarith
  · have hs' : |s|≤2 := le_of_not_gt hs
    have hb : |1-zeroValueBump s|≤1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr zeroValueBump.le_one)]
      linarith [zeroValueBump.nonneg (x:=s)]
    have hd : |deriv zeroValueBump s|≤D := hD _ (mem_range_self s)
    calc
      _ ≤ |1-zeroValueBump s|+|s*deriv zeroValueBump s| := by
        simpa only [valueCutoffSlope,sub_zero,zero_sub,abs_neg] using
          (abs_sub_le (1-zeroValueBump s) 0 (s*deriv zeroValueBump s))
      _ ≤ 1+2*D := by rw [abs_mul]; gcongr
      _ ≤ 2+2*D := by linarith

theorem eventually_large_nat_mul {t : ℝ} (ht : t≠0) :
    ∀ᶠ n:ℕ in atTop, 2 < |((n:ℝ)+1)*t| := by
  have hp : 0 < |t| := abs_pos.mpr ht
  obtain ⟨N,hN⟩ := exists_nat_gt (2/|t|)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hN' : 2<(N:ℝ)*|t| := (div_lt_iff₀ hp).mp hN
  have hn' : (N:ℝ)≤n := by exact_mod_cast hn
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤(n:ℝ)+1)]
  nlinarith

end OAI.Analysis.PDE.Variational
