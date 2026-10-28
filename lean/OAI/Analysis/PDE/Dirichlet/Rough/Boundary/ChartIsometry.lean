import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.ChartShift

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

variable {X E T : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [AddCommGroup T]

/-- The periodic chart deformation also works when chart coordinates and
physical coordinates are different isometric spaces. This is the transport
needed between Euclidean normal coordinates and the four-slot space. -/
theorem exists_periodic_chart_shift_isometry
    (e : X ≃ₗᵢ[ℝ] E) (L : T →+ E) (hLi : Function.Injective L)
    (hL : ∀ R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite)
    (r : E → ℝ) (hrp : ∀ x z, r (x + L z) = r x)
    {G : X → E} {P : E → X} (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P)
    {a : E} (hG0 : G 0 = a)
    (hinv : (fun z ↦ P (G z)) =ᶠ[𝓝 (0 : X)] id)
    (ℓ : X →L[ℝ] ℝ) (c : ℝ)
    (hlevel : ∀ z ∈ ball (0 : X) 1, r (G z) = c + ℓ z)
    (v : X) (hv : ℓ v = 0) :
    ∃ Φ : ℝ × E → E, ∃ d : ℝ, 0 < d ∧ ContDiff ℝ ∞ Φ ∧
      (∀ x, Φ (0, x) = x) ∧
      (∀ t : ℝ, |t| < d → Function.Bijective (fun x ↦ Φ (t, x))) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ Function.invFun (fun x ↦ Φ (p.1, x)) p.2)
        {p | |p.1| < d} ∧
      (∀ t x z, Φ (t, x + L z) = Φ (t, x) + L z) ∧
      (∀ t : ℝ, |t| < d → ∀ x, r (Φ (t, x)) = r x) ∧
      ((fun p : ℝ × X ↦ Φ (p.1, G p.2)) =ᶠ[𝓝 (0, (0 : X))]
        (fun p ↦ G (p.2 + p.1 • v))) := by
  let G' : E → E := G ∘ e.symm
  let P' : E → E := e ∘ P
  let ℓ' : E →L[ℝ] ℝ := ℓ.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hG' : ContDiff ℝ ∞ G' := hG.comp e.symm.toContinuousLinearEquiv.contDiff
  have hP' : ContDiff ℝ ∞ P' := e.toContinuousLinearEquiv.contDiff.comp hP
  have hzero : G' 0 = a := by simpa [G'] using hG0
  have hinv' : (fun z ↦ P' (G' z)) =ᶠ[𝓝 (0 : E)] id := by
    have ht : Tendsto e.symm (𝓝 (0 : E)) (𝓝 (0 : X)) := by
      simpa only [map_zero] using e.symm.continuous.tendsto (0 : E)
    filter_upwards [ht.eventually hinv] with z hz
    change e (P (G (e.symm z))) = z
    change P (G (e.symm z)) = e.symm z at hz
    rw [hz,e.apply_symm_apply]
  have hlevel' (z : E) (hz : z ∈ ball (0 : E) 1) : r (G' z) = c + ℓ' z := by
    apply hlevel
    simpa only [mem_ball,dist_zero_right,e.symm.norm_map] using hz
  have hv' : ℓ' (e v) = 0 := by simpa [ℓ'] using hv
  obtain ⟨Φ,d,hd,hΦ,hΦ0,hbij,hi,hper,hlev,hgerm⟩ :=
    exists_periodic_chart_shift L hLi hL r hrp hG' hP' hzero hinv' ℓ' c hlevel' (e v) hv'
  refine ⟨Φ,d,hd,hΦ,hΦ0,hbij,hi,hper,hlev,?_⟩
  have ht : Tendsto (fun p : ℝ × X ↦ (p.1,e p.2))
      (𝓝 (0,(0 : X))) (𝓝 (0,(0 : E))) := by
    simpa only [Function.comp_apply,map_zero] using
      (continuous_fst.prodMk (e.continuous.comp continuous_snd)).tendsto ((0 : ℝ),(0 : X))
  filter_upwards [ht.eventually hgerm] with p hp
  simpa only [G',Function.comp_apply,e.symm_apply_apply,map_add,map_smul] using hp

end OAI.Analysis.PDE.Dirichlet
