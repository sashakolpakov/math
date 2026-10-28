import OAI.Analysis.Fourier.WavePackets.AngularChart
import Mathlib.Geometry.Manifold.PartitionOfUnity

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set
open scoped ContDiff Manifold

theorem exists_positive_axis_rotation {d : ℕ} {ξ : Space (d + 1)} (hξ : ξ ≠ 0) :
    ∃ R : Space (d + 1) ≃ₗᵢ[ℝ] Space (d + 1), 0 < R ξ 0 := by
  let e : Space (d + 1) := EuclideanSpace.single 0 1
  have he : ‖e‖ = 1 := by simp [e]
  have hn : ‖ξ‖ = ‖‖ξ‖ • e‖ := by simp [norm_smul, he]
  let R : Space (d + 1) ≃ₗᵢ[ℝ] Space (d + 1) :=
    Submodule.reflection (ℝ ∙ (ξ - ‖ξ‖ • e))ᗮ
  have hR : R ξ = ‖ξ‖ • e := Submodule.reflection_sub hn
  refine ⟨R, ?_⟩
  rw [hR]
  simpa [e] using norm_pos_iff.mpr hξ

theorem compact_positive_axis_lower_bound {d : ℕ} {b : Space (d + 1) → ℂ}
    (hc : HasCompactSupport b) (hp : ∀ ξ ∈ tsupport b, 0 < ξ 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ ξ ∈ tsupport b, a ≤ ξ 0 := by
  by_cases hne : (tsupport b).Nonempty
  · have he : ContinuousOn (fun ξ : Space (d + 1) => ξ 0) (tsupport b) := by
      fun_prop
    obtain ⟨ξ, hξ, hmin⟩ := hc.exists_isMinOn hne he
    exact ⟨ξ 0, hp ξ hξ, hmin⟩
  · exact ⟨1, by norm_num, fun ξ hξ => False.elim (hne ⟨ξ, hξ⟩)⟩

/-- Any compact annular symbol has a fixed finite smooth atlas of
positive projective charts. Each chart comes with a genuine positive
lower bound for its longitudinal coordinate. -/
theorem finite_angular_atlas {d : ℕ} {φ : Space (d + 1) → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hz : 0 ∉ tsupport φ) :
    ∃ s : Finset (Space (d + 1) ≃ₗᵢ[ℝ] Space (d + 1)),
      ∃ b : s → Space (d + 1) → ℂ, ∃ a : s → ℝ,
      (∀ i, ContDiff ℝ ∞ (b i) ∧ HasCompactSupport (b i) ∧
        0 < a i ∧ (∀ ξ ∈ tsupport (b i), a i ≤ ξ 0) ∧
        tsupport (fun ξ => b i (i.val ξ)) ⊆ tsupport φ) ∧
      (fun ξ => ∑ i : s, b i (i.val ξ)) = φ := by
  classical
  let U := fun R : Space (d + 1) ≃ₗᵢ[ℝ] Space (d + 1) =>
    {ξ : Space (d + 1) | 0 < R ξ 0}
  have hU : ∀ R, IsOpen (U R) := by
    intro R
    apply isOpen_lt continuous_const
    fun_prop
  have hcover : tsupport φ ⊆ ⋃ R, U R := by
    intro ξ hξ
    have hξ0 : ξ ≠ 0 := by intro he; subst ξ; exact hz hξ
    obtain ⟨R, hR⟩ := exists_positive_axis_rotation hξ0
    exact mem_iUnion.mpr ⟨R, hR⟩
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover U hU hcover
  have hcover' : tsupport φ ⊆ ⋃ i : s, U i.val := by
    intro ξ hξ
    obtain ⟨R, hR⟩ := mem_iUnion.mp (hs hξ)
    obtain ⟨hRs, hξR⟩ := mem_iUnion.mp hR
    exact mem_iUnion.mpr ⟨⟨R, hRs⟩, hξR⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (𝓘(ℝ, Space (d + 1))) (isClosed_tsupport φ) (fun i : s => U i.val)
      (fun i => hU i.val) hcover'
  let g : s → Space (d + 1) → ℂ := fun i ξ => (ρ i ξ : ℂ) * φ ξ
  have hg (i : s) : ContDiff ℝ ∞ (g i) := by
    have hr : ContDiff ℝ ∞ (ρ i) := contMDiff_iff_contDiff.mp (ρ i).contMDiff
    exact (Complex.ofRealCLM.contDiff.comp hr).mul hφ
  have hgc (i : s) : HasCompactSupport (g i) := hc.mul_left
  have hgφ (i : s) : tsupport (g i) ⊆ tsupport φ := tsupport_mul_subset_right
  have hgU (i : s) : tsupport (g i) ⊆ U i.val := by
    apply Set.Subset.trans ?_ (hρ i)
    apply closure_minimal _ (isClosed_tsupport (ρ i))
    intro ξ hξ
    apply subset_tsupport (ρ i)
    intro he
    exact hξ (by simp [g, he])
  let b : s → Space (d + 1) → ℂ := fun i ξ => g i (i.val.symm ξ)
  have hbc (i : s) : HasCompactSupport (b i) :=
    (hgc i).comp_homeomorph i.val.symm.toHomeomorph
  have hbp (i : s) : ∀ ξ ∈ tsupport (b i), 0 < ξ 0 := by
    intro ξ hξ
    have hgξ : i.val.symm ξ ∈ tsupport (g i) :=
      tsupport_comp_subset_preimage (g i) i.val.symm.continuous hξ
    have ht := hgU i hgξ
    change 0 < i.val (i.val.symm ξ) 0 at ht
    simpa using ht
  choose a ha hamin using fun i => compact_positive_axis_lower_bound (hbc i) (hbp i)
  refine ⟨s, b, a, ?_, ?_⟩
  · intro i
    refine ⟨(hg i).comp i.val.symm.contDiff, hbc i, ha i, hamin i, ?_⟩
    have he : (fun ξ => b i (i.val ξ)) = g i := by
      funext ξ
      simp [b]
    rw [he]
    exact hgφ i
  · funext ξ
    change (∑ i : s, (ρ i (i.val.symm (i.val ξ)) : ℂ) *
      φ (i.val.symm (i.val ξ))) = φ ξ
    simp only [LinearIsometryEquiv.symm_apply_apply, ← Finset.sum_mul, ← Complex.ofReal_sum]
    by_cases hξ : φ ξ = 0
    · simp [hξ]
    · have hsum := ρ.sum_eq_one (subset_tsupport φ hξ)
      rw [finsum_eq_sum_of_fintype] at hsum
      rw [hsum]
      simp

end OAI.Analysis.Fourier.WavePackets
