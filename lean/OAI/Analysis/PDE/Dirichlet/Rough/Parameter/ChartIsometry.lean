import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.ChartShift

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

namespace ParameterDeformation

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
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
    (A : Z →L[ℝ] X) (hA : ∀ t, ℓ (A t) = 0) :
    ∃ Φ : Z × E → E, ∃ d : ℝ, 0 < d ∧ ContDiff ℝ ∞ Φ ∧
      (∀ x, Φ (0, x) = x) ∧
      (∀ t : Z, ‖t‖ < d → Function.Bijective (fun x ↦ Φ (t, x))) ∧
      ContDiffOn ℝ ∞ (fun p : Z × E ↦ Function.invFun (fun x ↦ Φ (p.1, x)) p.2)
        {p | ‖p.1‖ < d} ∧
      (∀ t x z, Φ (t, x + L z) = Φ (t, x) + L z) ∧
      (∀ t : Z, ‖t‖ < d → ∀ x, r (Φ (t, x)) = r x) ∧
      ((fun p : Z × X ↦ Φ (p.1, G p.2)) =ᶠ[𝓝 (0, (0 : X))]
        (fun p ↦ G (p.2 + A p.1))) := by
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
  let A' : Z →L[ℝ] E := e.toContinuousLinearEquiv.toContinuousLinearMap.comp A
  have hA' : ∀ t, ℓ' (A' t) = 0 := by
    intro t
    simpa [ℓ', A'] using hA t
  obtain ⟨Φ,d,hd,hΦ,hΦ0,hbij,hi,hper,hlev,hgerm⟩ :=
    ParameterDeformation.exists_periodic_chart_shift L hLi hL r hrp hG' hP' hzero hinv' ℓ' c hlevel' A' hA'
  refine ⟨Φ,d,hd,hΦ,hΦ0,hbij,hi,hper,hlev,?_⟩
  have ht : Tendsto (fun p : Z × X ↦ (p.1,e p.2))
      (𝓝 (0,(0 : X))) (𝓝 (0,(0 : E))) := by
    simpa only [Function.comp_apply,map_zero] using
      (continuous_fst.prodMk (e.continuous.comp continuous_snd)).tendsto ((0 : Z),(0 : X))
  filter_upwards [ht.eventually hgerm] with p hp
  simpa only [G',A',ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv,Function.comp_apply,e.symm_apply_apply,map_add] using hp

end ParameterDeformation
end OAI.Analysis.PDE.Dirichlet
