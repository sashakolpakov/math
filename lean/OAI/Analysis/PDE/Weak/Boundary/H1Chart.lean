import OAI.Analysis.PDE.Weak.Boundary.H1Pullback

/-! Zero-Dirichlet H¹ functions remain zero-Dirichlet H¹ functions under
a genuine smooth boundary chart. The chain rule is obtained from smooth
approximations in the actual L² graph, not postulated for weak derivatives. -/

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped Topology ENNReal ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem chartH1Pair_smooth
    {U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hU : IsOpen U)
    (G : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m) (hG : ContDiff ℝ ∞ G)
    {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hmap : Measure.map G (volume.restrict U) ≤ c • volume)
    {M : ℝ} (hM : ∀ y ∈ U, ‖chartGradientMap G y‖ ≤ M)
    (u ψ : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hu : ContDiff ℝ ∞ u) (hψ : ContDiff ℝ ∞ ψ)
    (hsu : HasCompactSupport u) (hsψ : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) (hψG : ∀ y ∈ U, ψ y = u (G y)) :
    chartH1Pair U hU.measurableSet G (hG.of_le (by simp)) hc hmap hM (smoothH1Pair u hu hsu) =
      smoothH1Pair ψ hψ hsψ := by
  have hq : Measure.QuasiMeasurePreserving G (volume.restrict U) volume :=
    ⟨hG.continuous.measurable, Measure.absolutelyContinuous_of_le_smul hmap⟩
  have hvalue := (ae_restrict_iff' hU.measurableSet).mp
    (hq.ae (smoothH1Pair_value_ae u hu hsu))
  have hgradient := (ae_restrict_iff' hU.measurableSet).mp
    (hq.ae (smoothH1Pair_gradient_ae u hu hsu))
  have hchain (y) (hy : y ∈ U) :
      OAI.Analysis.PDE.Variational.cellGradient ψ y = chartGradientMap G y (OAI.Analysis.PDE.Variational.cellGradient u (G y)) := by
    have he : ψ =ᶠ[𝓝 y] u ∘ G := by
      filter_upwards [hU.mem_nhds hy] with z hz
      exact hψG z hz
    have hh := cellGradient_comp_chart (hG.differentiable (by simp) y)
      (hu.differentiable (by simp) (G y))
    have heq : OAI.Analysis.PDE.Variational.cellGradient ψ y = OAI.Analysis.PDE.Variational.cellGradient (u ∘ G) y := by
      ext i
      exact congrArg (fun T => T (Pi.single i 1)) (he.fderiv_eq (𝕜 := ℝ))
    exact heq.trans hh
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [chartH1Pair_value_ae U hU.measurableSet G (hG.of_le (by simp)) hc hmap hM
        (smoothH1Pair u hu hsu), smoothH1Pair_value_ae ψ hψ hsψ, hvalue] with y hy hψy huy
    rw [hy, hψy]
    by_cases hh : y ∈ U
    · rw [indicator_of_mem hh, huy hh, hψG y hh]
    · rw [indicator_of_notMem hh, image_eq_zero_of_notMem_tsupport (fun ht => hh (hψU ht))]
  · apply Lp.ext
    filter_upwards [chartH1Pair_gradient_ae U hU.measurableSet G (hG.of_le (by simp)) hc hmap hM
        (smoothH1Pair u hu hsu), smoothH1Pair_gradient_ae ψ hψ hsψ, hgradient] with y hy hψy huy
    rw [hy, hψy]
    by_cases hh : y ∈ U
    · rw [indicator_of_mem hh, huy hh, hchain y hh]
    · rw [indicator_of_notMem hh]
      ext i
      simp only [PiLp.zero_apply, OAI.Analysis.PDE.Variational.cellGradient_apply,
        fderiv_of_notMem_tsupport ℝ (fun ht => hh (hψU ht)), zero_apply]

theorem H1Zero.chart_pullback
    {U V Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hU : IsOpen U) (hV : IsOpen V)
    (hUb : Bornology.IsBounded U) (hΩ : Ω ⊆ V)
    {G P : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m}
    (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P)
    (hGU : MapsTo G U V) (hPV : MapsTo P V U)
    (hPG : ∀ x ∈ U, P (G x) = x) (hGP : ∀ x ∈ V, G (P x) = x)
    {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hmap : Measure.map G (volume.restrict U) ≤ c • volume)
    {M : ℝ} (hM : ∀ y ∈ U, ‖chartGradientMap G y‖ ≤ M)
    {p : H1Pair m} (hp : p ∈ H1Zero Ω) :
    chartH1Pair U hU.measurableSet G (hG.of_le (by simp)) hc hmap hM p ∈
      H1Zero (U ∩ G ⁻¹' Ω) := by
  have hclosed : IsClosed {q : H1Pair m |
      chartH1Pair U hU.measurableSet G (hG.of_le (by simp)) hc hmap hM q ∈
        H1Zero (U ∩ G ⁻¹' Ω)} :=
    isClosed_closure.preimage (chartH1Pair U hU.measurableSet G (hG.of_le (by simp)) hc hmap hM).continuous
  apply closure_minimal (s := smoothH1Graph Ω) _ hclosed hp
  rintro q ⟨u, hu, hsu, huΩ, rfl⟩
  obtain ⟨ψ, hψ, hsψ, hψU, hψP, _⟩ :=
    exists_compact_chart_test hV hU hUb hP hG hPV hGP u hu hsu (huΩ.trans hΩ)
  have hψG : ∀ y ∈ U, ψ y = u (G y) := by
    intro y hy
    have hh := hψP (G y) (hGU hy)
    rwa [hPG y hy] at hh
  change chartH1Pair U hU.measurableSet G (hG.of_le (by simp)) hc hmap hM (smoothH1Pair u hu hsu) ∈
    H1Zero (U ∩ G ⁻¹' Ω)
  rw [chartH1Pair_smooth hU G hG hc hmap hM u ψ hu hψ hsu hsψ hψU hψG]
  apply smoothH1Pair_mem_H1Zero
  have hsupport : tsupport ψ ⊆ G ⁻¹' tsupport u := by
    apply closure_minimal _ ((isClosed_tsupport u).preimage hG.continuous)
    intro y hy
    have hyU : y ∈ U := hψU (subset_closure hy)
    apply subset_closure
    change u (G y) ≠ 0
    rwa [← hψG y hyU]
  intro y hy
  exact ⟨hψU hy, huΩ (hsupport hy)⟩

end OAI.Analysis.PDE.Weak
