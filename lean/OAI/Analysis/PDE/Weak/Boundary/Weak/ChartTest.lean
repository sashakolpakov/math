import OAI.Analysis.PDE.Green.LocalExtension

/-! Actual compact smooth tests transported through a local boundary
chart. A cutoff prevents the global formula for the inverse chart from
creating unwanted tests outside the physical coordinate patch. -/

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Weak

theorem exists_compact_chart_test
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {G P : E → E} (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P)
    (hGU : MapsTo G U V) (hinv : ∀ x ∈ U, P (G x) = x)
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    ∃ ψ : E → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ V ∧
      (∀ x ∈ U, ψ (G x) = φ x) ∧
      (∀ x ∈ U, (fderiv ℝ ψ (G x)).comp (fderiv ℝ G x) = fderiv ℝ φ x) := by
  have hKV : G '' tsupport φ ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    exact hGU (hφU hx)
  obtain ⟨χ, hχ, _, hχone, hχzero⟩ :=
    OAI.Analysis.PDE.Green.exists_smooth_cutoff_near_compact
      (hs.image hG.continuous) hV hKV (k := ⊤)
  let ψ := fun x => χ x * φ (P x)
  have hψ : ContDiff ℝ ∞ ψ := hχ.mul (hφ.comp hP)
  have hψV : tsupport ψ ⊆ V := by
    intro x hx
    by_contra hxV
    have he : ψ =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hχzero x hxV] with y hy
      simp [ψ, hy]
    exact (notMem_tsupport_iff_eventuallyEq.mpr he) hx
  have hψs : HasCompactSupport ψ :=
    isCompact_of_isClosed_isBounded isClosed_closure (hVb.subset hψV)
  have hψG (x) (hx : x ∈ U) : ψ (G x) = φ x := by
    by_cases hz : φ x = 0
    · simp [ψ, hinv x hx, hz]
    · have hxS : x ∈ tsupport φ := subset_tsupport φ hz
      have hc := (hχone (G x) ⟨x, hxS, rfl⟩).eq_of_nhds
      simp [ψ, hc, hinv x hx]
  refine ⟨ψ, hψ, hψs, hψV, hψG, ?_⟩
  intro x hx
  have he : (fun y => ψ (G y)) =ᶠ[𝓝 x] φ := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hψG y hy
  have hc := ((hψ.differentiable (by simp) (G x)).hasFDerivAt.comp x
    (hG.differentiable (by simp) x).hasFDerivAt).fderiv
  exact hc.symm.trans he.fderiv_eq

end OAI.Analysis.PDE.Weak
