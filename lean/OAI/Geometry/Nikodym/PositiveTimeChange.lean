import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.OpenPartialHomeomorph.Basic

noncomputable section

namespace OAI.Geometry.Nikodym

open Set Filter _root_.MeasureTheory
open scoped Topology

/-- The elapsed time associated to a positive scalar speed. -/
def positiveTimePrimitive (q : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..s, (q u)⁻¹

@[simp] theorem positiveTimePrimitive_zero (q : ℝ → ℝ) :
    positiveTimePrimitive q 0 = 0 := by
  simp [positiveTimePrimitive]

theorem positiveTimePrimitive_hasStrictDerivAt {q : ℝ → ℝ} {l r : ℝ}
    (hq : Continuous q) (hl : l < 0) (hr : 1 < r)
    (hpos : ∀ s ∈ Ioo l r, 0 < q s) {s : ℝ} (hs : s ∈ Ioo l r) :
    HasStrictDerivAt (positiveTimePrimitive q) (q s)⁻¹ s := by
  have h0 : (0 : ℝ) ∈ Ioo l r := ⟨hl, by linarith⟩
  have hi : uIcc (0 : ℝ) s ⊆ Ioo l r := by
    intro u hu
    rcases mem_uIcc.mp hu with hu | hu
    · exact ⟨lt_of_lt_of_le h0.1 hu.1, lt_of_le_of_lt hu.2 hs.2⟩
    · exact ⟨lt_of_lt_of_le hs.1 hu.1, lt_of_le_of_lt hu.2 h0.2⟩
  have hc : ContinuousOn (fun u => (q u)⁻¹) (uIcc (0 : ℝ) s) :=
    hq.continuousOn.inv₀ (fun u hu => (hpos u (hi hu)).ne')
  have hcs : ContinuousAt (fun u => (q u)⁻¹) s :=
    hq.continuousAt.inv₀ (hpos s hs).ne'
  exact intervalIntegral.integral_hasStrictDerivAt_right hc.intervalIntegrable
    (hq.measurable.inv.stronglyMeasurable.stronglyMeasurableAtFilter) hcs

theorem positiveTimePrimitive_strictMonoOn {q : ℝ → ℝ} {l r : ℝ}
    (hq : Continuous q) (hl : l < 0) (hr : 1 < r)
    (hpos : ∀ s ∈ Ioo l r, 0 < q s) :
    StrictMonoOn (positiveTimePrimitive q) (Ioo l r) := by
  have hd : ∀ x ∈ Ioo l r, HasStrictDerivAt (positiveTimePrimitive q) (q x)⁻¹ x :=
    fun _ hx => positiveTimePrimitive_hasStrictDerivAt hq hl hr hpos hx
  apply strictMonoOn_of_deriv_pos (convex_Ioo l r)
    (fun x hx => (hd x hx).hasDerivAt.continuousAt.continuousWithinAt)
  intro x hx
  have hx' : x ∈ Ioo l r := interior_subset hx
  rw [(hd x hx').hasDerivAt.deriv]
  exact inv_pos.mpr (hpos x hx')

/-- A nonvanishing strict derivative makes an injective function on an open
interval into an open partial homeomorphism with that exact source. -/
theorem exists_openPartialHomeomorph_of_strictDeriv {f f' : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hi : InjOn f U)
    (hd : ∀ x ∈ U, HasStrictDerivAt f (f' x) x)
    (hn : ∀ x ∈ U, f' x ≠ 0) :
    ∃ T : OpenPartialHomeomorph ℝ ℝ, T.source = U ∧ (T : ℝ → ℝ) = f := by
  let e : PartialEquiv ℝ ℝ := hi.toPartialEquiv f U
  have hc : ContinuousOn e e.source :=
    fun x hx => (hd x hx).hasDerivAt.continuousAt.continuousWithinAt
  have ho : IsOpenMap (e.source.domRestrict e) := by
    intro V hV
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨x, hx, rfl⟩
    have hW : IsOpen (Subtype.val '' V : Set ℝ) :=
      hU.isOpenMap_subtype_val V hV
    have hm : Subtype.val '' V ∈ 𝓝 (x : ℝ) :=
      hW.mem_nhds ⟨x, hx, rfl⟩
    have hh : f '' (Subtype.val '' V) ∈ map f (𝓝 (x : ℝ)) :=
      Filter.image_mem_map hm
    rw [(hd x x.property).map_nhds_eq (hn x x.property)] at hh
    change (fun z : e.source => f z) '' V ∈ 𝓝 (f x)
    simpa only [Set.image_image] using hh
  exact ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict e hc ho hU, rfl, rfl⟩

theorem positive_timeChange_interval (T : OpenPartialHomeomorph ℝ ℝ)
    {l r : ℝ} (hsource : T.source = Ioo l r) (hl : l < 0) (hr : 1 < r)
    (hzero : T 0 = 0) (hmono : StrictMonoOn T T.source) :
    0 < T 1 ∧ Icc 0 (T 1) ⊆ T.target ∧
      T.symm '' Icc 0 (T 1) = Icc 0 1 := by
  have hsub : Icc (0 : ℝ) 1 ⊆ T.source := by
    intro s hs
    rw [hsource]
    exact ⟨lt_of_lt_of_le hl hs.1, lt_of_le_of_lt hs.2 hr⟩
  have h0 : (0 : ℝ) ∈ T.source := hsub ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ T.source := hsub ⟨zero_le_one, le_rfl⟩
  have ht : 0 < T 1 := by simpa only [hzero] using hmono h0 h1 zero_lt_one
  have hpre : ∀ t ∈ Icc 0 (T 1), ∃ s ∈ Icc (0 : ℝ) 1, T s = t := by
    intro t ht
    apply intermediate_value_Icc zero_le_one (T.continuousOn.mono hsub)
    simpa only [hzero] using ht
  have htarget : Icc 0 (T 1) ⊆ T.target := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := hpre t ht
    exact T.map_source (hsub hs)
  refine ⟨ht, htarget, ?_⟩
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨s, hs, rfl⟩ := hpre t ht
    simpa only [T.left_inv (hsub hs)] using hs
  · intro hs
    refine ⟨T s, ?_, T.left_inv (hsub hs)⟩
    constructor
    · simpa only [hzero] using hmono.monotoneOn h0 (hsub hs) hs.1
    · exact hmono.monotoneOn (hsub hs) h1 hs.2

/-- Integrating reciprocal speed gives an actual increasing time coordinate,
with an inverse whose derivative is the original speed. -/
theorem exists_positive_timeChange {q : ℝ → ℝ} {l r : ℝ}
    (hq : Continuous q) (hl : l < 0) (hr : 1 < r)
    (hpos : ∀ s ∈ Ioo l r, 0 < q s) :
    ∃ T : OpenPartialHomeomorph ℝ ℝ,
      T.source = Ioo l r ∧
      (∀ s, T s = ∫ u in (0 : ℝ)..s, (q u)⁻¹) ∧
      T 0 = 0 ∧ StrictMonoOn T T.source ∧
      (∀ s ∈ T.source, HasDerivAt T (q s)⁻¹ s) ∧
      (∀ t ∈ T.target, HasDerivAt T.symm (q (T.symm t)) t) ∧
      IsConnected T.target ∧ 0 < T 1 ∧
      Icc 0 (T 1) ⊆ T.target ∧ T.symm '' Icc 0 (T 1) = Icc 0 1 := by
  have hd : ∀ x ∈ Ioo l r, HasStrictDerivAt (positiveTimePrimitive q) (q x)⁻¹ x :=
    fun _ hx => positiveTimePrimitive_hasStrictDerivAt hq hl hr hpos hx
  have hm := positiveTimePrimitive_strictMonoOn hq hl hr hpos
  obtain ⟨T, hsource, hfun⟩ := exists_openPartialHomeomorph_of_strictDeriv
    isOpen_Ioo hm.injOn hd (fun x hx => inv_ne_zero (hpos x hx).ne')
  have htzero : T 0 = 0 := by rw [hfun]; exact positiveTimePrimitive_zero q
  have htmono : StrictMonoOn T T.source := by rw [hsource, hfun]; exact hm
  have htderiv : ∀ s ∈ T.source, HasDerivAt T (q s)⁻¹ s := by
    intro s hs
    rw [hfun]
    exact (hd s (hsource ▸ hs)).hasDerivAt
  have hinverse : ∀ t ∈ T.target, HasDerivAt T.symm (q (T.symm t)) t := by
    intro t ht
    have hs := T.map_target ht
    have hi : ∀ᶠ y in 𝓝 t, T (T.symm y) = y := by
      filter_upwards [T.open_target.mem_nhds ht] with y hy
      exact T.right_inv hy
    have hh := (htderiv (T.symm t) hs).of_local_left_inverse
      (T.symm.continuousAt ht) (inv_ne_zero (hpos _ (hsource ▸ hs)).ne') hi
    simpa only [inv_inv] using hh
  have hc : IsConnected T.target := by
    rw [← T.image_source_eq_target]
    apply IsConnected.image
    · rw [hsource]
      exact isConnected_Ioo (lt_trans hl (lt_trans zero_lt_one hr))
    · exact T.continuousOn
  obtain ⟨htpos, htsub, htimage⟩ :=
    positive_timeChange_interval T hsource hl hr htzero htmono
  refine ⟨T, hsource, ?_, htzero, htmono, htderiv, hinverse, hc, htpos, htsub, htimage⟩
  intro s
  change T s = positiveTimePrimitive q s
  rw [hfun]

end OAI.Geometry.Nikodym
