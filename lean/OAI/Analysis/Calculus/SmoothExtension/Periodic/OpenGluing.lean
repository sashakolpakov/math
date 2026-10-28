import OAI.Analysis.Calculus.SmoothExtension.Periodic.Infinity

/-! Smooth periodic gluing on an open parameter region. No regularity is
asserted at the boundary of the parameter region. -/
noncomputable section
open Set Filter Function TopologicalSpace
open scoped Topology ContDiff Manifold
namespace OAI.Analysis.Calculus.SmoothExtension

variable {Z E T : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup T]

omit [FiniteDimensional ℝ E] in
theorem exists_periodic_smooth_on_parameter_region
    (L : T →+ E) (θ : E → Z) (hθ : ContDiff ℝ ∞ θ)
    (hθper : ∀ x t, θ (x + L t) = θ x)
    {Ω : Set Z} (hΩ : IsOpen Ω) (K : Set E) (u : E → ℝ)
    (hl : ∀ z ∈ Ω, ∃ V : Set Z, IsOpen V ∧ z ∈ V ∧
      ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ (∀ x t, g (x + L t) = g x) ∧
        ∀ x ∈ K, θ x ∈ Ω ∩ V → g x = u x) :
    ∃ g : E → ℝ, ContDiffOn ℝ ∞ g (θ ⁻¹' Ω) ∧
      (∀ x t, g (x + L t) = g x) ∧ ∀ x ∈ K, θ x ∈ Ω → g x = u x := by
  classical
  let A : Opens Z := ⟨Ω, hΩ⟩
  let B : Opens E := ⟨θ ⁻¹' Ω, hΩ.preimage hθ.continuous⟩
  let : LocallyCompactSpace A := ChartedSpace.locallyCompactSpace Z A
  choose V hV hzV v hv hvper heq using (fun z : A ↦ hl z z.property)
  let W : A → Set A := fun z ↦ Subtype.val ⁻¹' V z
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (𝓘(ℝ,Z)) isClosed_univ W
    (fun z ↦ (hV z).preimage continuous_subtype_val)
    (fun z _ ↦ mem_iUnion.mpr ⟨z, hzV z⟩)
  let π : B → A := fun x ↦ ⟨θ x, x.property⟩
  have hπ : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,Z)) ∞ π := by
    rw [← ContMDiff.subtypeVal_comp_iff]
    exact hθ.contMDiff.comp contMDiff_subtype_val
  let f : B → ℝ := fun x ↦ ∑ᶠ z : A, ρ z (π x) • v z x
  have hf : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℝ)) ∞ f := by
    apply contMDiff_finsum
    · intro z
      exact ((ρ z).contMDiff.comp hπ).smul ((hv z).contMDiff.comp contMDiff_subtype_val)
    · exact (ρ.locallyFinite.preimage_continuous hπ.continuous).subset
        (fun z x hx ↦ by
          change ρ z (π x) ≠ 0
          exact fun h ↦ hx (by simp [h]))
  let g : E → ℝ := fun x ↦ if hx : θ x ∈ Ω then f ⟨x,hx⟩ else 0
  have hgB (x : B) : g x = f x := by
    have hx : θ (x : E) ∈ Ω := x.property
    simp only [g, dite_eq_left hx]
  refine ⟨g, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,ℝ)) ∞ (fun y : B ↦ g y) ⟨x,hx⟩ := by
      have he : (fun y : B ↦ g y) = f := funext hgB
      rw [he]
      exact hf.contMDiffAt
    exact (contMDiffAt_subtype_iff.mp hx').contDiffAt.contDiffWithinAt
  · intro x t
    by_cases hx : θ x ∈ Ω
    · have hxt : θ (x + L t) ∈ Ω := by rw [hθper]; exact hx
      simp only [g, dite_eq_left hx, dite_eq_left hxt, f]
      apply finsum_congr
      intro z
      have hp : π ⟨x + L t,hxt⟩ = π ⟨x,hx⟩ := Subtype.ext (hθper x t)
      rw [hp, hvper]
    · have hxt : θ (x + L t) ∉ Ω := by rw [hθper]; exact hx
      simp only [g, dite_eq_right hx, dite_eq_right hxt]
  · intro x hxK hxΩ
    rw [show g x = f ⟨x,hxΩ⟩ from hgB ⟨x,hxΩ⟩]
    change (∑ᶠ z : A, ρ z (π ⟨x,hxΩ⟩) • v z x) = u x
    calc
      _ = ∑ᶠ z : A, ρ z (π ⟨x,hxΩ⟩) • u x := by
        apply finsum_congr
        intro z
        by_cases hz : ρ z (π ⟨x,hxΩ⟩) = 0
        · simp only [hz, zero_smul]
        · rw [heq z x hxK ⟨hxΩ, hρ z (subset_tsupport _ hz)⟩]
      _ = (∑ z ∈ ρ.finsupport (π ⟨x,hxΩ⟩), ρ z (π ⟨x,hxΩ⟩)) • u x := by
        rw [← ρ.sum_finsupport_smul_eq_finsum _ (fun _ _ ↦ u x), Finset.sum_smul]
      _ = u x := by rw [ρ.sum_finsupport _ (mem_univ _), one_smul]

end OAI.Analysis.Calculus.SmoothExtension
