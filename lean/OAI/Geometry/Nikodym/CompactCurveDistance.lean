import OAI.Geometry.Nikodym.Chart.Geometry

noncomputable section
open Set Metric

namespace OAI.Geometry.Nikodym

theorem infDist_range_eq_sInf {J X : Type*} [Nonempty J] [PseudoMetricSpace X]
    (f : J → X) (x : X) :
    infDist x (range f) = sInf ((fun t => dist x (f t)) '' (univ : Set J)) := by
  have hglb : IsGLB ((fun t => dist x (f t)) '' (univ : Set J))
      (infDist x (range f)) := by
    have he : (fun y => dist x y) '' range f =
        (fun t => dist x (f t)) '' (univ : Set J) := by
      ext z
      constructor
      · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
        exact ⟨t, mem_univ _, rfl⟩
      · rintro ⟨t, _, rfl⟩
        exact ⟨f t, ⟨t, rfl⟩, rfl⟩
    rw [← he]
    exact isGLB_infDist (range_nonempty f)
  exact (hglb.csInf_eq (Set.Nonempty.image _ Set.univ_nonempty)).symm

/-- Distance to a continuously varying compact curve is jointly continuous
in the curve parameter and the point. -/
theorem continuous_infDist_range_compact
    {P J X : Type*} [TopologicalSpace P] [TopologicalSpace J]
    [CompactSpace J] [Nonempty J] [PseudoMetricSpace X]
    (γ : P × J → X) (hγ : Continuous γ) :
    Continuous (fun q : P × X => infDist q.2 (range (fun t => γ (q.1, t)))) := by
  let d : (P × X) → J → ℝ := fun q t => dist q.2 (γ (q.1, t))
  have hd : Continuous (Function.uncurry d) := by
    exact continuous_fst.snd.dist
      (hγ.comp (continuous_fst.fst.prodMk continuous_snd))
  have H := isCompact_univ.continuous_sInf (f := d) hd
  simpa only [infDist_range_eq_sInf, d] using H

/-- The analogous statement for a fixed compact parameter set, including
closed time intervals. -/
theorem continuous_infDist_image_compact
    {P J X : Type*} [TopologicalSpace P] [TopologicalSpace J]
    [PseudoMetricSpace X] {K : Set J} (hK : IsCompact K) (hne : K.Nonempty)
    (γ : P × J → X) (hγ : ContinuousOn γ (univ ×ˢ K)) :
    Continuous (fun q : P × X => infDist q.2 ((fun t => γ (q.1, t)) '' K)) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : Nonempty K := hne.to_subtype
  let γ' : P × K → X := fun q => γ (q.1, q.2)
  have hc : Continuous γ' := by
    apply hγ.comp_continuous
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    intro q
    exact ⟨mem_univ _, q.2.property⟩
  have H := continuous_infDist_range_compact γ' hc
  convert H using 1
  funext q
  congr 1
  ext x
  simp only [mem_image, mem_range, γ', Subtype.exists, exists_prop]

theorem metricTube_eq_infDist_sublevel {X : Type*} [MetricSpace X]
    {A : Set X} (hA : A.Nonempty) (δ : ℝ) :
    metricTube δ A = {x | infDist x A < δ} := by
  ext x
  exact (infDist_lt_iff hA).symm

/-- Open membership in a compact varying curve's metric tube, with the
spatial point varying as well. -/
theorem isOpen_compact_curve_tube
    {P J X : Type*} [TopologicalSpace P] [TopologicalSpace J]
    [CompactSpace J] [Nonempty J] [MetricSpace X]
    (γ : P × J → X) (hγ : Continuous γ) (δ : ℝ) :
    IsOpen {q : P × X | q.2 ∈ metricTube δ (range (fun t => γ (q.1, t)))} := by
  simp_rw [metricTube_eq_infDist_sublevel (range_nonempty _), Set.mem_ofPred_eq]
  exact isOpen_lt (continuous_infDist_range_compact γ hγ) continuous_const

end OAI.Geometry.Nikodym
