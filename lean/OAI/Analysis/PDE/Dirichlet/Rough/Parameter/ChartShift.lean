import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.ChartCutoffs
import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.PeriodicInverse

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

namespace ParameterDeformation

open OAI.Analysis.Calculus.SmoothExtension OAI.Analysis.PDE.Elliptic

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
variable {E T : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [AddCommGroup T]

/-- Genuine periodic boundary-preserving chart translations. The family has
an actual jointly smooth inverse, and agrees with an ordinary tangential
translation in a neighborhood of the chosen chart center. -/
theorem exists_periodic_chart_shift
    (L : T →+ E) (hLi : Function.Injective L)
    (hL : ∀ R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite)
    (r : E → ℝ) (hrp : ∀ x z, r (x + L z) = r x)
    {G P : E → E} (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P)
    {a : E} (hG0 : G 0 = a)
    (hinv : (fun z ↦ P (G z)) =ᶠ[𝓝 (0 : E)] id)
    (ℓ : E →L[ℝ] ℝ) (c : ℝ)
    (hlevel : ∀ z ∈ ball (0 : E) 1, r (G z) = c + ℓ z)
    (A : Z →L[ℝ] E) (hA : ∀ t, ℓ (A t) = 0) :
    ∃ Φ : Z × E → E, ∃ d : ℝ, 0 < d ∧ ContDiff ℝ ∞ Φ ∧
      (∀ x, Φ (0, x) = x) ∧
      (∀ t : Z, ‖t‖ < d → Function.Bijective (fun x ↦ Φ (t, x))) ∧
      ContDiffOn ℝ ∞ (fun p : Z × E ↦ Function.invFun (fun x ↦ Φ (p.1, x)) p.2)
        {p | ‖p.1‖ < d} ∧
      (∀ t x z, Φ (t, x + L z) = Φ (t, x) + L z) ∧
      (∀ t : Z, ‖t‖ < d → ∀ x, r (Φ (t, x)) = r x) ∧
      ((fun p : Z × E ↦ Φ (p.1, G p.2)) =ᶠ[𝓝 (0, (0 : E))]
        (fun p ↦ G (p.2 + A p.1))) := by
  classical
  obtain ⟨hPa, R₀, hR₀, U, hU, haU, hRU, hGP, hPU⟩ :=
    OAI.Analysis.PDE.Elliptic.exists_inverse_chart_neighborhood (hP.of_le (by simp)) (hG.of_le (by simp))
      hG0 hinv (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨gap, hgap, hgapL⟩ := OAI.Analysis.Calculus.SmoothExtension.exists_positive_period_gap L hLi hL
  let R : ℝ := min R₀ (gap/4)
  have hR : 0 < R := lt_min hR₀ (by positivity)
  have hRR : R ≤ R₀ := min_le_left _ _
  have hRg : 2 * R < gap := by
    have : R ≤ gap/4 := min_le_right _ _
    linarith
  let K : Set E := closedBall a R
  have hK : IsCompact K := isCompact_closedBall a R
  have hdis : ∀ x z w, x + L z ∈ K → x + L w ∈ K → z = w :=
    disjoint_period_translates_of_radius L hgapL hRg a
  obtain ⟨ρ, η, hρ, hη, hηc, hρoff, hηW, hplateau, hρone, hηone⟩ :=
    exists_nested_chart_cutoffs hG.continuous hG0 hR
  have hρU : Function.support ρ ⊆ U := by
    intro x hx
    have hdist : dist x a < R := by
      by_contra hn
      exact hx (hρoff x (le_of_not_gt hn))
    exact hRU (hdist.le.trans hRR)
  let h : Z × E → E := fun p ↦ chartShiftDisplacement G P ρ η (A p.1) 1 p.2
  have hh : ContDiff ℝ ∞ h := by
    simp only [h, chartShiftDisplacement, cutoffShift, one_mul]
    fun_prop
  have hs : ∀ t x, x ∉ K → h (t, x) = 0 := by
    intro t x hx
    exact chartShiftDisplacement_eq_zero G P ρ η (A t) 1
      (hρoff x (le_of_not_ge hx))
  have hz : ∀ x, h (0, x) = 0 := by
    intro x
    simp only [h, chartShiftDisplacement, cutoffShift, map_zero, smul_zero,
      add_zero, sub_self]
  obtain ⟨d₀, hd₀, hb, hInv⟩ := ParameterDeformation.exists_smooth_periodic_deformation_inverse L hL hK hdis h hh hs hz
  let s : Z × E → E := fun p ↦ η p.2 • A p.1
  have hsmooth : ContDiff ℝ ∞ s :=
    (hη.comp contDiff_snd).smul (A.contDiff.comp contDiff_fst)
  have hsoff : ∀ t x, x ∉ tsupport η → s (t, x) = 0 := by
    intro t x hx
    simp only [s, image_eq_zero_of_notMem_tsupport hx, zero_smul]
  have hszero : ∀ x, s (0, x) = 0 := by
    intro x
    simp only [s, map_zero, smul_zero]
  obtain ⟨d₁, hd₁, hsb, _⟩ :=
    ParameterDeformation.exists_smooth_compact_deformation_inverse hsmooth hηc hsoff hszero
  let d : ℝ := min d₀ d₁
  have hd : 0 < d := lt_min hd₀ hd₁
  let Φ : Z × E → E := fun p ↦ periodicPerturbation L (fun x ↦ h (p.1, x)) p.2
  have hΦ : ContDiff ℝ ∞ Φ :=
    contDiff_snd.add (ParameterDeformation.contDiff_parametricPeriodization L hL hK h hs hh)
  refine ⟨Φ, d, hd, hΦ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change x + (∑' z, h (0, x + L z)) = x
    simp only [hz, tsum_zero, add_zero]
  · intro t ht
    exact hb t (ht.trans_le (min_le_left _ _))
  · apply hInv.mono
    intro p hp
    change ‖p.1‖ < d₀
    exact (show ‖p.1‖ < d from hp).trans_le (min_le_left _ _)
  · intro t x z
    exact periodicPerturbation_add L _ z x
  · intro t ht x
    apply periodicPerturbation_preserves_level L _ r (hs t) hdis hrp
    intro y
    apply chartShiftDisplacement_preserves_level G P ρ η r (A t) 1 hρU hηW hPU hGP
    · intro z hz hne
      rw [← hGP z hz]
      exact hplateau (P z) hne
    · change Function.Injective (fun x ↦ x + (1 * η x) • A t)
      simp only [one_mul]
      exact (hsb t (ht.trans_le (min_le_right _ _))).injective
    · exact hlevel
    · exact hA t
  · have hρG : (fun z ↦ ρ (G z)) =ᶠ[𝓝 (0 : E)] fun _ ↦ 1 := by
      exact hρone.comp_tendsto (by simpa only [hG0] using hG.continuous.tendsto (0 : E))
    have hGK : ∀ᶠ z in 𝓝 (0 : E), G z ∈ K := by
      have hbK : K ∈ 𝓝 a := closedBall_mem_nhds a hR
      exact (show Tendsto G (𝓝 (0 : E)) (𝓝 a) by
        simpa only [hG0] using hG.continuous.tendsto (0 : E)).eventually hbK
    filter_upwards [(continuous_snd.tendsto (0, (0 : E))).eventually hinv,
      (continuous_snd.tendsto (0, (0 : E))).eventually hρG,
      (continuous_snd.tendsto (0, (0 : E))).eventually hηone,
      (continuous_snd.tendsto (0, (0 : E))).eventually hGK] with p hpg hrho heta hgk
    change periodicPerturbation L (fun x ↦ h (p.1, x)) (G p.2) = _
    have he := periodicPerturbation_at L (fun x ↦ h (p.1, x)) (hs p.1) hdis
      (G p.2) 0 (by simpa only [map_zero, add_zero] using hgk)
    simp only [map_zero, add_zero] at he
    rw [he]
    change G p.2 + ρ (G p.2) • (G (cutoffShift η (A p.1) 1 (P (G p.2))) - G (P (G p.2))) = _
    change P (G p.2) = p.2 at hpg
    rw [hrho, one_smul, hpg]
    simp only [cutoffShift, heta, one_mul, one_smul, add_sub_cancel]

end ParameterDeformation
end OAI.Analysis.PDE.Dirichlet
