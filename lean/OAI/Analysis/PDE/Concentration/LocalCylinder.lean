import OAI.Analysis.PDE.Concentration.Cylinder.Average
import OAI.Analysis.PDE.Concentration.SmoothExtension

namespace OAI.Analysis.PDE.Concentration

open Set Filter Laplacian InnerProductSpace
open scoped ContDiff Topology

/-- Logarithmic radial propagation for a genuinely local smooth
superharmonic function. The global smooth extension is constructed internally. -/
theorem cylinderAverage_logarithmic_lower_on {f : CylinderSpace → ℝ} {U : Set CylinderSpace}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hdom : ∀ r ∈ Icc a 3, ∀ t ∈ Icc (-cylinderTimeEnd) cylinderTimeEnd,
      ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), cylinderPoint t r θ ∈ U)
    (hnonneg : ∀ r ∈ Icc a 3, ∀ t ∈ Icc (-cylinderTimeEnd) cylinderTimeEnd,
      ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), 0 ≤ f (cylinderPoint t r θ))
    (hΔ : ∀ r ∈ Ioo a 3, ∀ t ∈ Icc (-cylinderTimeEnd) cylinderTimeEnd,
      ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), Δ f (cylinderPoint t r θ) ≤ 0) :
    cylinderAverage f a * (Real.log 3 / (4 * (Real.log 3 - Real.log a))) ≤
      cylinderAverage f 1 := by
  let P : Set (ℝ × ℝ × ℝ) := Icc (-cylinderTimeEnd) cylinderTimeEnd ×ˢ
    (Icc a 3 ×ˢ Icc (0 : ℝ) (2 * Real.pi))
  let K : Set CylinderSpace := (fun p : ℝ × ℝ × ℝ => cylinderPoint p.1 p.2.1 p.2.2) '' P
  have hK : IsCompact K := (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).image
    contDiff_cylinderPoint.continuous
  have hKU : K ⊆ U := by
    rintro x ⟨p, hp, rfl⟩
    exact hdom p.2.1 hp.2.1 p.1 hp.1 p.2.2 hp.2.2
  obtain ⟨F, hF, he⟩ := exists_global_smooth_eq_near_closed hK.isClosed hU hKU hf
  have hpoint {r t θ : ℝ} (hr : r ∈ Icc a 3) (ht : t ∈ Icc (-cylinderTimeEnd) cylinderTimeEnd)
      (hθ : θ ∈ Icc (0 : ℝ) (2 * Real.pi)) : F =ᶠ[nhds (cylinderPoint t r θ)] f :=
    he _ ⟨(t, r, θ), ⟨ht, hr, hθ⟩, rfl⟩
  have hresult := cylinderAverage_logarithmic_lower hF ha ha1
    (fun r hr t ht θ hθ => by rw [(hpoint hr ht hθ).self_of_nhds]; exact hnonneg r hr t ht θ hθ)
    (fun r hr t ht θ hθ => by
      rw [(laplacian_congr_nhds (hpoint (Ioo_subset_Icc_self hr) ht hθ)).self_of_nhds]
      exact hΔ r hr t ht θ hθ)
  have heavg (r : ℝ) (hr : r ∈ Icc a 3) : cylinderAverage F r = cylinderAverage f r :=
    cylinderAverage_congr (fun _ ht _ hθ => (hpoint hr ht hθ).self_of_nhds)
  rw [heavg a ⟨le_rfl, by linarith⟩, heavg 1 ⟨ha1.le, by norm_num⟩] at hresult
  exact hresult

end OAI.Analysis.PDE.Concentration
