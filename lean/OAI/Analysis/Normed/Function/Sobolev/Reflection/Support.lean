import OAI.Analysis.Normed.Function.Sobolev.Reflection.Extension

open Set Filter _root_.MeasureTheory
noncomputable section
namespace OAI.Analysis.Normed.Function.Sobolev

variable {d N : ℕ}

def reflectedSupport (k : Fin d) (a : Fin N → ℝ) (K : Set (Fin d → ℝ)) :
    Set (Fin d → ℝ) := K ∪ ⋃j, normalScale k (a j)⁻¹ '' K

theorem isCompact_reflectedSupport (k : Fin d) (a : Fin N → ℝ)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) : IsCompact (reflectedSupport k a K) :=
  hK.union (isCompact_iUnion (fun j ↦ hK.image (normalScale k (a j)⁻¹).continuous))

theorem reflectionExtension_zero_off (k : Fin d) (a c : Fin N → ℝ)
    (ha : ∀j, a j ≠ 0) {u : (Fin d → ℝ) → ℝ} {K : Set (Fin d → ℝ)}
    (hu : ∀ᵐx, x ∉ K → u x = 0) :
    ∀ᵐx, x ∉ reflectedSupport k a K → reflectionExtension k a c u x = 0 := by
  have htrans (j : Fin N) : ∀ᵐx, normalScale k (a j) x ∉ K →
      u (normalScale k (a j) x) = 0 := (normalScale_quasiMeasurePreserving k (ha j)).ae hu
  have hall : ∀ᵐx, ∀j, normalScale k (a j) x ∉ K →
      u (normalScale k (a j) x) = 0 := by
    exact ae_all_iff.mpr htrans
  filter_upwards [hu, hall] with x hx ht
  intro hnot
  have hxK : x ∉ K := fun h ↦ hnot (Or.inl h)
  have hj (j : Fin N) : normalScale k (a j) x ∉ K := by
    intro h
    apply hnot
    right
    apply mem_iUnion.mpr
    refine ⟨j,normalScale k (a j) x,h,?_⟩
    simp [normalScale_comp,ha j]
  simp only [reflectionExtension]
  have hz := hx hxK
  have ht0 (j : Fin N) := ht j (hj j)
  simp [indicator_apply,hz,ht0]

theorem integrable_of_memLp_two_compact_support_pi {u : (Fin d → ℝ) → ℝ}
    (hu : MemLp u 2) {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    (hs : ∀ᵐx, x ∉ K → u x = 0) : Integrable u := by
  have : IsFiniteMeasure (volume.restrict K) :=
    ⟨by simpa using hK.measure_lt_top (μ := volume)⟩
  have hi : IntegrableOn u K := (hu.restrict K).integrable (by norm_num)
  have he : u =ᵐ[volume] K.indicator u := by
    filter_upwards [hs] with x hx
    by_cases h : x ∈ K
    · simp [h]
    · simp [h,hx h]
  exact (hi.integrable_indicator hK.measurableSet).congr he.symm

end OAI.Analysis.Normed.Function.Sobolev
