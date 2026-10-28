import OAI.Analysis.Calculus.SmoothExtension.ExtensionInfinityChart
import OAI.Analysis.Calculus.SmoothExtension.ExtensionInfinityLocal
import OAI.Analysis.PDE.Elliptic.Calculus.SmoothCoordinateChart
import OAI.Analysis.PDE.Elliptic.PeriodicChartCoverage

/-! A genuine global C∞ extension from a smooth regular closed sublevel. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace OAI.Analysis.Calculus.SmoothExtension

open OAI.Analysis.PDE.Elliptic

variable {m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
local notation "E" => EuclideanSpace ℝ (Fin m)

theorem exists_local_smooth_extension_regular_sublevel (hm : 0 < m)
    (r : E → ℝ) (hr : ContDiff ℝ ∞ r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f {x | r x ≤ 0})
    (a : E) (ha : r a ≤ 0) :
    ∃ W : Set E, IsOpen W ∧ a ∈ W ∧
      ∃ g : E → F, ContDiffOn ℝ ∞ g W ∧ ∀ x ∈ W, r x ≤ 0 → g x = f x := by
  by_cases hlt : r a < 0
  · refine ⟨{x | r x < 0},isOpen_lt hr.continuous continuous_const,hlt,
      f,hf.mono (fun x hx => (show r x ≤ 0 from le_of_lt hx)),?_⟩
    intro x hx hxr
    rfl
  · have hra : r a = 0 := le_antisymm ha (le_of_not_gt hlt)
    let k : Fin m := ⟨0,hm⟩
    obtain ⟨c,C,G,P,hc,hC,hG,hP,hG0,hchart⟩ :=
      OAI.Analysis.PDE.Elliptic.exists_smooth_bounded_coordinate_chart k hr a (hreg a hra) isOpen_univ (mem_univ a)
    have hinv := (hchart 0 (mem_closedBall_self (by norm_num))).2.1
    obtain ⟨hPa,R,hR,V,hV,haV,hRV,hGP,hPV⟩ :=
      OAI.Analysis.PDE.Elliptic.exists_inverse_chart_neighborhood (hP.of_le (by simp)) (hG.of_le (by simp))
        hG0 hinv (show (0:ℝ)<1 by norm_num)
    have hside : ∀ z ∈ ball (0:E) 2, r (G z) ≤ 0 ↔ 0 ≤ z k := by
      intro z hz
      have he := (hchart z (ball_subset_closedBall hz)).2.2.1
      rw [hra,sub_zero] at he
      rw [he]
      constructor <;> intro h <;> nlinarith
    obtain ⟨W,hW,haW,g,hg,hgf⟩ := exists_smooth_extension_in_chart k r f hf
      G P hG hP hPa isOpen_ball (mem_ball_self (by norm_num)) hV haV hGP hside
    exact ⟨W,hW,haW,g,hg.contDiffOn,hgf⟩

theorem exists_smooth_extension_regular_sublevel (hm : 0 < m)
    (r : E → ℝ) (hr : ContDiff ℝ ∞ r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f {x | r x ≤ 0}) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ ∀ x, r x ≤ 0 → g x = f x := by
  apply exists_smooth_extension_of_local_on (isClosed_le hr.continuous continuous_const) f
  intro x hx
  obtain ⟨W,hW,hxW,g,hg,hgf⟩ := exists_local_smooth_extension_regular_sublevel hm r hr hreg f hf x hx
  exact ⟨W,hW,hxW,g,hg,fun y hy => hgf y hy.2 hy.1⟩

end OAI.Analysis.Calculus.SmoothExtension
