import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Stability
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.DataCauchy

/-! Genuine C²,β Cauchy estimates for Newtonian solutions of mollified C^α data. -/

noncomputable section
open _root_.MeasureTheory Set Metric Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

def mollifiedNewtonianPotential {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ) (k : ℕ) :=
  newtonianPotential (smoothData (standardMollifier m k) f)

theorem contDiff_mollifiedNewtonianPotential {m : ℕ} (hm : 1 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifiedNewtonianPotential f k) :=
  contDiff_newtonianPotential hm _ (contDiff_smoothData _ f hf) (hasCompactSupport_smoothData _ f hfc)

theorem mollifiedNewtonianPotential_cauchy {m : ℕ} (hm : 2 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    {H α β : ℝ} (hH : 0 ≤ H) (hβ : 0 < β) (hβα : β < α) (hα1 : α < 1)
    (hh : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) :
    ∃ r : ℕ → ℝ, (∀ k, 0 ≤ r k) ∧ Tendsto r atTop (𝓝 0) ∧ ∀ k l,
      (∀ x, |mollifiedNewtonianPotential f k x - mollifiedNewtonianPotential f l x| ≤ r k + r l) ∧
      (∀ x, ‖fderiv ℝ (mollifiedNewtonianPotential f k) x - fderiv ℝ (mollifiedNewtonianPotential f l) x‖ ≤ r k + r l) ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ (mollifiedNewtonianPotential f k)) x -
        fderiv ℝ (fderiv ℝ (mollifiedNewtonianPotential f l)) x‖ ≤ r k + r l) ∧
      (∀ x y, ‖(fderiv ℝ (fderiv ℝ (mollifiedNewtonianPotential f k)) x -
        fderiv ℝ (fderiv ℝ (mollifiedNewtonianPotential f l)) x) -
        (fderiv ℝ (fderiv ℝ (mollifiedNewtonianPotential f k)) y -
        fderiv ℝ (fderiv ℝ (mollifiedNewtonianPotential f l)) y)‖ ≤
        (r k + r l) * ‖x - y‖ ^ β) := by
  obtain ⟨s, hs, hsT, hdata⟩ := smoothData_pairwise_bounds f hf hfc hH hβ hβα hh
  obtain ⟨C, hC, hc⟩ := newtonian_solution_stability hm hβ (hβα.trans hα1)
  refine ⟨fun k => 3 * C * s k, fun k => mul_nonneg (by positivity) (hs k), ?_, ?_⟩
  · simpa using hsT.const_mul (3 * C)
  · intro k l
    obtain ⟨hholder, hsup, hL1⟩ := hdata k l
    obtain ⟨hv, hg, hhess, hhessH⟩ := hc
      (smoothData (standardMollifier m k) f) (smoothData (standardMollifier m l) f)
      ((contDiff_smoothData _ f hf).of_le (by simp)) ((contDiff_smoothData _ f hf).of_le (by simp))
      (hasCompactSupport_smoothData _ f hfc) (hasCompactSupport_smoothData _ f hfc)
      (s k + s l) (s k + s l) (s k + s l) (add_nonneg (hs k) (hs l)) (add_nonneg (hs k) (hs l)) (add_nonneg (hs k) (hs l))
      hholder hsup hL1
    have he : C * (s k + s l + (s k + s l) + (s k + s l)) = 3 * C * s k + 3 * C * s l := by ring
    have he' : C * (s k + s l) ≤ 3 * C * s k + 3 * C * s l := by
      nlinarith [mul_nonneg hC.le (hs k), mul_nonneg hC.le (hs l)]
    refine ⟨fun x => (hv x).trans_eq he, fun x => (hg x).trans_eq he,
      fun x => (hhess x).trans_eq he, ?_⟩
    intro x y
    exact (hhessH x y).trans (mul_le_mul_of_nonneg_right he' (Real.rpow_nonneg (norm_nonneg _) _))

theorem mollifiedNewtonianPotential_tendsto {m : ℕ} (hm : 2 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    {H α : ℝ} (hH : 0 ≤ H) (hα : 0 < α)
    (hh : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α)
    (x : EuclideanSpace ℝ (Fin m)) :
    Tendsto (fun k => mollifiedNewtonianPotential f k x) atTop (𝓝 (newtonianPotential f x)) := by
  obtain ⟨V, hV, hL1⟩ := standardMollifier_integral_error f hf hfc hH hα.le hh
  let e (k : ℕ) := H * (standardMollifier m k).rOut ^ α
  let B := rieszBallMass (volume : Measure (EuclideanSpace ℝ (Fin m))) 2
  have ht : Tendsto (fun k => (B + V) * e k) atTop (𝓝 0) := by
    simpa [e] using (((standardMollifier_radius_tendsto m).rpow_const_nhds_zero hα).const_mul H).const_mul (B + V)
  have hb (k : ℕ) : |mollifiedNewtonianPotential f k x - newtonianPotential f x| ≤ (B + V) * e k := by
    let q := fun y => smoothData (standardMollifier m k) f y - f y
    have hq : Continuous q := (contDiff_smoothData _ f hf).continuous.sub hf
    have hqc : HasCompactSupport q := (hasCompactSupport_smoothData _ f hfc).sub hfc
    have hu := smoothData_error (standardMollifier m k) f hf hH hα.le hh
    have he0 : 0 ≤ e k := mul_nonneg hH (Real.rpow_nonneg (standardMollifier m k).rOut_pos.le α)
    have h := newtonianPotential_bound hm q (hq.integrable_of_hasCompactSupport hqc) he0 hu (hL1 k) x
    dsimp only [q] at h
    rw [newtonianPotential_sub (show 1 ≤ m by omega) _ f (contDiff_smoothData _ f hf).continuous hf
      (hasCompactSupport_smoothData _ f hfc) hfc] at h
    exact h.trans_eq (by dsimp [B, e]; ring)
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [ht.eventually (Iio_mem_nhds hε)] with k hk
  rw [dist_eq_norm, Real.norm_eq_abs]
  exact (hb k).trans_lt hk

end OAI.Analysis.PDE.Schauder
