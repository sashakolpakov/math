import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.MeanValue

/-! # Parametric Flow -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.ParametricFlow.Abelian

noncomputable section

/-!
Construct a local flow with continuous dependence on an external
parameter. Picard-Lindelöf is applied to the enlarged autonomous vector
field `(p,v) ↦ (0,F(p,v))`; uniqueness of a function with zero derivative
shows that the constructed flow keeps the parameter fixed.
-/

open Set _root_.Metric
open scoped _root_.Topology NNReal

variable {P V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Local solutions depend continuously on the parameter, initial vector,
and time. The differential equation uses the unchanged initial parameter. -/
theorem exists_continuous_parametric_flow
    (F : P × V → V) (u₀ : P × V) (hF : ContDiffAt ℝ 1 F u₀) :
    ∃ (r : ℝ≥0), 0 < r ∧ ∃ ε : ℝ, 0 < ε ∧
      ∃ flow : (P × V) × ℝ → V,
        ContinuousOn flow (closedBall u₀ r ×ˢ Ioo (-ε) ε) ∧
        ∀ u ∈ closedBall u₀ r, flow (u, 0) = u.2 ∧
          ∀ t ∈ Ioo (-ε) ε,
            HasDerivAt (fun τ => flow (u, τ)) (F (u.1, flow (u, t))) t := by
  let G : P × V → P × V := fun u => (0, F u)
  have hG : ContDiffAt ℝ 1 G u₀ := contDiffAt_const.prodMk hF
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hG
  obtain ⟨α, hα, hc⟩ := (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  have hα₀ (u : P × V) (hu : u ∈ closedBall u₀ r) : α (u, 0) = u := (hα u hu).1
  have hd (u : P × V) (hu : u ∈ closedBall u₀ r) (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      HasDerivAt (fun τ => α (u, τ)) (G (α (u, t))) t := by
    have ht' : t ∈ Ioo (0 - ε) (0 + ε) := by simpa only [zero_sub, zero_add] using ht
    exact ((hα u hu).2 t (Ioo_subset_Icc_self ht')).hasDerivAt
      (Icc_mem_nhds ht'.1 ht'.2)
  have hparam (u : P × V) (hu : u ∈ closedBall u₀ r) (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      (α (u, t)).1 = u.1 := by
    have hp (s : ℝ) (hs : s ∈ Ioo (-ε) ε) :
        HasDerivAt (fun τ => (α (u, τ)).1) 0 s := (hd u hu s hs).fst
    have he := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-ε) ε).isPreconnected
      (fun s hs => (hp s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hp s hs).deriv) ht (show (0 : ℝ) ∈ Ioo (-ε) ε by constructor <;> linarith)
    exact he.trans (congrArg Prod.fst (hα₀ u hu))
  refine ⟨r, hr, ε, hε, fun q => (α q).2, ?_, ?_⟩
  · apply hc.snd.mono
    rintro ⟨u, t⟩ ⟨hu, ht⟩
    exact ⟨hu, by simpa only [zero_sub, zero_add] using Ioo_subset_Icc_self ht⟩
  · intro u hu
    refine ⟨congrArg Prod.snd (hα₀ u hu), ?_⟩
    intro t ht
    have h := (hd u hu t ht).snd
    change HasDerivAt (fun τ => (α (u, τ)).2) (F (α (u, t))) t at h
    have hp : α (u, t) = (u.1, (α (u, t)).2) :=
      Prod.ext (hparam u hu t ht) rfl
    rw [hp] at h
    exact h

theorem exists_continuous_parametric_flow_zero
    (F : P × V → V) (p₀ : P) (hF : ContDiffAt ℝ 1 F (p₀, 0)) :
    ∃ (r : ℝ≥0), 0 < r ∧ ∃ ε : ℝ, 0 < ε ∧
      ∃ flow : P × ℝ → V,
        ContinuousOn flow (closedBall p₀ r ×ˢ Ioo (-ε) ε) ∧
        ∀ p ∈ closedBall p₀ r, flow (p, 0) = 0 ∧
          ∀ t ∈ Ioo (-ε) ε,
            HasDerivAt (fun τ => flow (p, τ)) (F (p, flow (p, t))) t := by
  obtain ⟨r, hr, ε, hε, α, hc, hα⟩ := exists_continuous_parametric_flow F (p₀, 0) hF
  have hball (p : P) (hp : p ∈ closedBall p₀ r) :
      (p, (0 : V)) ∈ closedBall (p₀, 0) r := by
    simpa only [mem_closedBall, Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hp
  refine ⟨r, hr, ε, hε, fun q => α ((q.1, 0), q.2), ?_, ?_⟩
  · apply hc.comp ((continuous_fst.prodMk continuous_const).prodMk continuous_snd).continuousOn
    rintro ⟨p, t⟩ ⟨hp, ht⟩
    exact ⟨hball p hp, ht⟩
  · intro p hp
    exact hα (p, 0) (hball p hp)

end

end OAI.ArithmeticGeometry.Descent.CMVariety.ParametricFlow.Abelian
