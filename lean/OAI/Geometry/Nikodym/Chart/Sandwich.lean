import OAI.Geometry.Nikodym.Chart.Average
import OAI.Geometry.Nikodym.Chart.Geometry

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Geometry.Nikodym


theorem metricTube_unitSegment {n : ℕ} (r : ℝ) (v c : Space n) :
    metricTube r (OAI.MeasureTheory.Kakeya.unitSegment v c) = OAI.MeasureTheory.Kakeya.tube r v c := by
  ext x
  constructor
  · rintro ⟨y,⟨t,ht,rfl⟩,hd⟩
    exact OAI.MeasureTheory.Kakeya.mem_tube_iff.mpr ⟨t,ht,hd⟩
  · intro h
    obtain ⟨t,ht,hd⟩ := OAI.MeasureTheory.Kakeya.mem_tube_iff.mp h
    exact ⟨c+t•v,⟨t,ht,rfl⟩,hd⟩

/-- The actual bi-Lipschitz chart supplies precisely the tube sandwich used
by the maximal estimate. Its inner margin is retained in the statement. -/
theorem bilipschitz_chart_tube_sandwich {M : Type*} [MetricSpace M] {n : ℕ}
    {F : M → Space n} {G : Space n → M} {S I : Set M} {V : Set (Space n)}
    {K L : NNReal} (hK : 0<K) (hL : 0<L)
    (hF : LipschitzOnWith K F S) (hG : LipschitzOnWith L G V)
    (hI : I⊆S) (hmap : MapsTo F S V) (hback : MapsTo G V S)
    (hGF : ∀ x∈S,G (F x)=x) (hFG : ∀ y∈V,F (G y)=y)
    {l δ : ℝ} (hl : 0≤l) (hl1 : l≤1) {v c : Space n}
    (hsegment : F '' I = OAI.MeasureTheory.Kakeya.unitSegment (l•v) c)
    (hmargin : OAI.MeasureTheory.Kakeya.tube (δ/(L:ℝ)) (l•v) c⊆V) :
    OAI.MeasureTheory.Kakeya.tube (δ/(L:ℝ)) (l•v) c ⊆ F '' (metricTube δ I ∩ S) ∧
    F '' (metricTube δ I ∩ S) ⊆ OAI.MeasureTheory.Kakeya.tube ((K:ℝ)*δ) v c := by
  constructor
  · have H := metricTube_inter_subset_image hG hI hmap hGF hFG hback
      (r := δ/(L:ℝ)) hL
    rw [hsegment,metricTube_unitSegment] at H
    have he : (L:ℝ)*(δ/(L:ℝ))=δ := by
      field_simp
    rw [he] at H
    intro x hx
    exact H ⟨hx,hmargin hx⟩
  · have H := image_metricTube_subset hF hI (r := δ) hK
    rw [hsegment,metricTube_unitSegment] at H
    exact H.trans (shortTube_subset_unitTube hl hl1 ((K:ℝ)*δ) v c)

/-- Equality of the true restricted-tube integral and its chart image. -/
theorem lintegral_image_eq {M : Type*} [MeasurableSpace M] {n : ℕ}
    (μ : Measure M) {F : M → Space n} (hF : Measurable F)
    {S T : Set M} (hTS : T⊆S) (hinj : InjOn F S)
    (himage : MeasurableSet (F '' T)) (g : Space n → ℂ) (hg : Measurable g) :
    (∫⁻ y in F '' T,‖g y‖ₑ ∂(Measure.map F (μ.restrict S))) =
      ∫⁻ x in T,‖g (F x)‖ₑ ∂μ := by
  rw [setLIntegral_map himage hg.enorm hF,Measure.restrict_restrict (himage.preimage hF)]
  have heq : F ⁻¹' (F '' T) ∩ S = T := by
    ext x
    constructor
    · rintro ⟨⟨y,hy,he⟩,hxS⟩
      have hxy := hinj (hTS hy) hxS he
      exact hxy ▸ hy
    · intro hx
      exact ⟨⟨x,hx,rfl⟩,hTS hx⟩
  rw [heq]

theorem measure_image_eq {M : Type*} [MeasurableSpace M] {n : ℕ}
    (μ : Measure M) {F : M → Space n} (hF : Measurable F)
    {S T : Set M} (hTS : T⊆S) (hinj : InjOn F S)
    (himage : MeasurableSet (F '' T)) :
    Measure.map F (μ.restrict S) (F '' T) = μ T := by
  rw [Measure.map_apply hF himage,Measure.restrict_apply (himage.preimage hF)]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨y,hy,he⟩,hxS⟩
    exact (hinj (hTS hy) hxS he) ▸ hy
  · intro hx
    exact ⟨⟨x,hx,rfl⟩,hTS hx⟩

end OAI.Geometry.Nikodym
