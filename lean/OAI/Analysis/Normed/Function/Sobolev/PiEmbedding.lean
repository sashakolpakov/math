import OAI.Analysis.Normed.Function.Sobolev.CompactEmbedding
import OAI.Analysis.PDE.Weak.SobolevWeakTransport

open OAI.Analysis.Fourier.Wave

open Set _root_.MeasureTheory Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.Normed.Function.Sobolev

open OAI.Analysis.PDE.Weak

/-- The compact-support Sobolev embedding in the raw finite Pi coordinates
used by the weak elliptic equation. -/
theorem exists_contDiff_pi_representative_of_compact_derivative_family {d k q : ℕ}
    (hd : 0 < d) (hk : d + q < k)
    (U : List (Fin d) → (Fin d → ℝ) → ℝ) {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    (hUK : ∀ α, α.length ≤ k → ∀ᵐ x, x ∉ K → U α x = 0)
    (hU2 : ∀ α, α.length ≤ k → MemLp (U α) 2)
    (hUD : ∀ α, α.length < k → ∀ i : Fin d,
      OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivative volume (Pi.single i 1) (U α) (U (i :: α))) :
    ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ q g ∧ U [] =ᵐ[volume] g := by
  let e : Space d ≃L[ℝ] (Fin d → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d ↦ ℝ)
  have he : MeasurePreserving e := PiLp.volume_preserving_ofLp (Fin d)
  have hei : MeasurePreserving e.symm := PiLp.volume_preserving_toLp (Fin d)
  let V : List (Fin d) → Space d → ℝ := fun α ↦ U α ∘ e
  have hVK (α : List (Fin d)) (hα : α.length ≤ k) :
      ∀ᵐ x, x ∉ e.symm '' K → V α x = 0 := by
    filter_upwards [he.quasiMeasurePreserving.ae (hUK α hα)] with x hx
    intro hnot
    apply hx
    intro hmem
    exact hnot ⟨e x, hmem, e.symm_apply_apply x⟩
  have hVD (α : List (Fin d)) (hα : α.length < k) (i : Fin d) :
      OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivative volume (EuclideanSpace.single i 1) (V α) (V (i :: α)) := by
    apply OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivative.comp_measurePreserving_equiv e he
    have hs : e (EuclideanSpace.single i 1) = Pi.single i 1 := by
      rfl
    rw [hs]
    exact hUD α hα i
  obtain ⟨g, hg, hgeq⟩ := exists_contDiff_representative_of_compact_derivative_family hd hk V
    (hK.image e.symm.continuous) hVK (fun α hα ↦ (hU2 α hα).comp_measurePreserving he) hVD
  refine ⟨g ∘ e.symm, hg.comp e.symm.contDiff, ?_⟩
  have h := hei.quasiMeasurePreserving.ae hgeq
  filter_upwards [h] with x hx
  simpa only [V, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using hx

theorem exists_contDiff_pi_representative_of_compact_L2_derivatives {d k q : ℕ}
    (hd : 0 < d) (hk : d + q < k)
    (U : List (Fin d) → Lp ℝ 2 (volume : Measure (Fin d → ℝ)))
    {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    (hUK : ∀ α, α.length ≤ k → ∀ᵐ x, x ∉ K → U α x = 0)
    (hUD : ∀ α, α.length < k → ∀ i : Fin d,
      OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivative volume (Pi.single i 1) (U α) (U (i :: α))) :
    ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ q g ∧ (U [] : (Fin d → ℝ) → ℝ) =ᵐ[volume] g := by
  exact exists_contDiff_pi_representative_of_compact_derivative_family hd hk
    (fun α ↦ U α) hK hUK (fun α _ ↦ Lp.memLp (U α)) hUD

theorem exists_C2_pi_representative_of_compact_derivative_family {d k : ℕ}
    (hd : 0 < d) (hk : d + 2 < k)
    (U : List (Fin d) → (Fin d → ℝ) → ℝ) {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    (hUK : ∀ α, α.length ≤ k → ∀ᵐ x, x ∉ K → U α x = 0)
    (hU2 : ∀ α, α.length ≤ k → MemLp (U α) 2)
    (hUD : ∀ α, α.length < k → ∀ i : Fin d,
      OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivative volume (Pi.single i 1) (U α) (U (i :: α))) :
    ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ 2 g ∧ U [] =ᵐ[volume] g :=
  exists_contDiff_pi_representative_of_compact_derivative_family hd hk U hK hUK hU2 hUD

theorem exists_C2_pi_representative_of_compact_L2_derivatives {d k : ℕ}
    (hd : 0 < d) (hk : d + 2 < k)
    (U : List (Fin d) → Lp ℝ 2 (volume : Measure (Fin d → ℝ)))
    {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    (hUK : ∀ α, α.length ≤ k → ∀ᵐ x, x ∉ K → U α x = 0)
    (hUD : ∀ α, α.length < k → ∀ i : Fin d,
      OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivative volume (Pi.single i 1) (U α) (U (i :: α))) :
    ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ 2 g ∧ (U [] : (Fin d → ℝ) → ℝ) =ᵐ[volume] g :=
  exists_contDiff_pi_representative_of_compact_L2_derivatives hd hk U hK hUK hUD

end OAI.Analysis.Normed.Function.Sobolev
