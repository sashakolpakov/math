import OAI.Analysis.Normed.Function.Sobolev.CoordinateDecay

open OAI.Analysis.Fourier.Wave

open Set _root_.MeasureTheory FourierTransform Filter InnerProductSpace
open scoped Topology BigOperators
noncomputable section
namespace OAI.Analysis.Normed.Function.Sobolev

open OAI.Analysis.PDE.Weak

theorem integrable_of_memLp_two_compact_support {d : ℕ} {u : Space d → ℝ}
    (hu : MemLp u 2) {K : Set (Space d)} (hK : IsCompact K)
    (hs : ∀ᵐ x, x ∉ K → u x = 0) : Integrable u := by
  have : IsFiniteMeasure (volume.restrict K) :=
    ⟨by simpa using hK.measure_lt_top (μ := volume)⟩
  have hi : IntegrableOn u K := (hu.restrict K).integrable (by norm_num)
  have he : u =ᵐ[volume] K.indicator u := by
    filter_upwards [hs] with x hx
    by_cases h : x ∈ K
    · simp [h]
    · simp [h, hx h]
  exact (hi.integrable_indicator hK.measurableSet).congr he.symm

/-- A compactly supported family of genuine L² weak derivatives of order
strictly above `dimension + q` has a real C^q representative. No continuity of
the original L² representative and no Fourier decay assumption is needed. -/
theorem exists_contDiff_representative_of_compact_derivative_family {d k q : ℕ}
    (hd : 0 < d) (hk : d + q < k)
    (U : List (Fin d) → Space d → ℝ) {K : Set (Space d)} (hK : IsCompact K)
    (hUK : ∀ α, α.length ≤ k → ∀ᵐ x, x ∉ K → U α x = 0)
    (hU2 : ∀ α, α.length ≤ k → MemLp (U α) 2)
    (hUD : ∀ α, α.length < k → ∀ i : Fin d,
      OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivative volume (EuclideanSpace.single i 1) (U α) (U (i :: α))) :
    ∃ g : Space d → ℝ, ContDiff ℝ q g ∧ U [] =ᵐ[volume] g := by
  have hUi (α : List (Fin d)) (hα : α.length ≤ k) : Integrable (U α) :=
    integrable_of_memLp_two_compact_support (hU2 α hα) hK (hUK α hα)
  let N : ℝ := ∫ x, ‖U [] x‖
  let M : ℝ := ∑ i : Fin d, ∫ x, ‖U (List.replicate k i) x‖
  have hN : 0 ≤ N := integral_nonneg fun _ ↦ norm_nonneg _
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ ↦ integral_nonneg fun _ ↦ norm_nonneg _
  have hcoord (i : Fin d) (ξ : Space d) :
      |ξ i| ^ k * ‖realFourier (U []) ξ‖ ≤ M := by
    have h := coordinate_fourier_decay i (fun j ↦ U (List.replicate j i)) hK
      (fun j hj ↦ hUK _ (by simpa using hj))
      (fun j hj ↦ hUi _ (by simpa using hj))
      (fun j hj ↦ by
        simpa only [List.replicate_succ] using
          hUD (List.replicate j i) (by simpa using hj) i) ξ
    simp only [List.replicate_zero] at h
    refine h.trans ?_
    exact Finset.single_le_sum
      (f := fun j : Fin d ↦ ∫ x : Space d, ‖U (List.replicate k j) x‖)
      (fun j _ ↦ integral_nonneg fun x ↦ norm_nonneg _)
      (Finset.mem_univ i)
  have hpoly := polynomial_decay_of_coordinate_bounds hd (realFourier (U [])) hN hM
    (norm_realFourier_le (U [])) hcoord
  obtain ⟨g, hg, hgeq⟩ := exists_contDiff_representative_of_polynomial_fourier_decay
    (hUi [] (by simp)).ofReal (hU2 [] (by simp)).ofReal
    (show 0 ≤ 2 ^ k * (N + (d : ℝ) ^ k * M) by positivity) hk hpoly
  refine ⟨fun x ↦ (g x).re, Complex.reCLM.contDiff.comp hg, ?_⟩
  filter_upwards [hgeq] with x hx
  simpa using congrArg Complex.re hx

theorem exists_C2_representative_of_compact_derivative_family {d k : ℕ}
    (hd : 0 < d) (hk : d + 2 < k)
    (U : List (Fin d) → Space d → ℝ) {K : Set (Space d)} (hK : IsCompact K)
    (hUK : ∀ α, α.length ≤ k → ∀ᵐ x, x ∉ K → U α x = 0)
    (hU2 : ∀ α, α.length ≤ k → MemLp (U α) 2)
    (hUD : ∀ α, α.length < k → ∀ i : Fin d,
      OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivative volume (EuclideanSpace.single i 1) (U α) (U (i :: α))) :
    ∃ g : Space d → ℝ, ContDiff ℝ 2 g ∧ U [] =ᵐ[volume] g :=
  exists_contDiff_representative_of_compact_derivative_family hd hk U hK hUK hU2 hUD

end OAI.Analysis.Normed.Function.Sobolev
