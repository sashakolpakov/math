import OAI.Geometry.Nikodym.Chart.Maximal
import OAI.Geometry.Nikodym.Chart.Sandwich

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Geometry.Nikodym


def metricTubeMaximal {M : Type*} [MetricSpace M] [MeasurableSpace M] {ι : Type*}
    (μ : Measure M) (S : Set M) (I : M → ι → Set M)
    (admissible : M → ι → Prop) (δ : ℝ) (f : M → ℂ) (x : M) : ℝ≥0∞ :=
  ⨆ i, ⨆ (_ : admissible x i),
    (∫⁻ y in metricTube δ (I x i) ∩ S,‖f y‖ₑ ∂μ) / μ (metricTube δ (I x i) ∩ S)

theorem metricTubeMaximal_congr_ae {M : Type*} [MetricSpace M] [MeasurableSpace M]
    {ι : Type*} {μ : Measure M} {S : Set M} {f g : M → ℂ}
    (hfg : f =ᵐ[μ.restrict S] g) (I : M → ι → Set M)
    (admissible : M → ι → Prop) (δ : ℝ) :
    metricTubeMaximal μ S I admissible δ f = metricTubeMaximal μ S I admissible δ g := by
  funext x
  apply iSup_congr
  intro i
  apply iSup_congr
  intro hi
  congr 1
  apply lintegral_congr_ae
  exact (ae_restrict_of_ae_restrict_of_subset inter_subset_right hfg).mono
    (fun y hy => congrArg (fun z : ℂ => ‖z‖ₑ) hy)

theorem chart_image_measurable {M : Type*} [MeasurableSpace M] {n : ℕ}
    {F : M → Space n} {G : Space n → M} {S T : Set M} {V : Set (Space n)}
    (hG : Measurable G) (hV : MeasurableSet V) (hT : MeasurableSet T) (hTS : T⊆S)
    (hmap : MapsTo F S V) (hGF : ∀ x∈S,G (F x)=x) (hFG : ∀ y∈V,F (G y)=y) :
    MeasurableSet (F '' T) := by
  have heq : F '' T = V ∩ G ⁻¹' T := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨hmap (hTS hx),by simpa only [mem_preimage,hGF x (hTS hx)] using hx⟩
    · rintro ⟨hy,hGy⟩
      exact ⟨G y,hGy,hFG y hy⟩
  rw [heq]
  exact hV.inter (hT.preimage hG)

/-- Exact pointwise domination of the genuine metric-tube maximal function
under a local bi-Lipschitz chart. The domain restriction and tube margin are
explicit; no global coordinate system is required. -/
theorem metricTubeMaximal_le_chart {M : Type*} [MetricSpace M] [MeasurableSpace M]
    [BorelSpace M] {n : ℕ} {ι : Type*} (μ : Measure M)
    {F : M → Space n} {G : Space n → M} {S : Set M} {V : Set (Space n)}
    (hS : MeasurableSet S) (hV : MeasurableSet V)
    (hFm : Measurable F) (hGm : Measurable G)
    {K L : NNReal} (hK : 1≤K) (hL : 1≤L)
    (hF : LipschitzOnWith K F S) (hG : LipschitzOnWith L G V)
    (hmap : MapsTo F S V) (hback : MapsTo G V S)
    (hGF : ∀ x∈S,G (F x)=x) (hFG : ∀ y∈V,F (G y)=y)
    {a b : ℝ≥0∞} (ha : a≠⊤) (hb : b≠⊤)
    (hup : Measure.map F (μ.restrict S)≤b • volume)
    (hdown : volume.restrict V≤a • Measure.map F (μ.restrict S))
    {δ l₀ : ℝ} (hδ : 0<δ) (hl₀ : 0<l₀)
    (I : M → ι → Set M) (admissible : M → ι → Prop)
    (hI : ∀ x∈S,∀ i,admissible x i →
      I x i⊆S ∧ x∈I x i ∧ ∃ l v c,l₀≤l ∧ l≤1 ∧ ‖v‖=1 ∧
        F '' I x i=OAI.MeasureTheory.Kakeya.unitSegment (l•v) c ∧ OAI.MeasureTheory.Kakeya.tube (δ/(L:ℝ)) (l•v) c⊆V)
    (g : Space n → ℂ) (hg : Measurable g) {x : M} (hx : x∈S) :
    metricTubeMaximal μ S I admissible δ (g ∘ F) x ≤
      (a*b*ENNReal.ofReal (((K:ℝ)*(L:ℝ))^n*(l₀^n)⁻¹))*
        nikodymMaximal ((K:ℝ)*δ) g (F x) := by
  have hKp : 0<K := lt_of_lt_of_le zero_lt_one hK
  have hLp : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hLr : (0:ℝ)<L := hLp
  have hR : (1:ℝ)≤(K:ℝ)*(L:ℝ) := by
    have hKr : (1:ℝ)≤K := hK
    have hLr : (1:ℝ)≤L := hL
    nlinarith
  have he : ((K:ℝ)*(L:ℝ))*(δ/(L:ℝ))=(K:ℝ)*δ := by field_simp
  have hinj : InjOn F S := by
    intro x hx y hy hxy
    simpa only [hGF x hx,hGF y hy] using congrArg G hxy
  apply iSup_le
  intro i
  apply iSup_le
  intro hi
  obtain ⟨hIS,hxI,l,v,c,hl,hl1,hv,hseg,hmar⟩ := hI x hx i hi
  have htm : MeasurableSet (metricTube δ (I x i) ∩ S) := by
    rw [metricTube_eq_thickening]
    exact Metric.isOpen_thickening.measurableSet.inter hS
  have him := chart_image_measurable hGm hV htm inter_subset_right hmap hGF hFG
  obtain ⟨hin,hout⟩ := bilipschitz_chart_tube_sandwich hKp hLp hF hG hIS hmap hback hGF hFG
    (hl₀.trans_le hl).le hl1 hseg hmar
  have hFx : F x∈OAI.MeasureTheory.Kakeya.unitSegment (l•v) c := hseg ▸ mem_image_of_mem F hxI
  have H := chartTube_average_le_nikodym ha hb hup hdown (div_pos hδ hLr) hR
    hl₀ hl hl1 hv hFx hin hmar (by simpa only [he] using hout) g
  rw [he,lintegral_image_eq μ hFm inter_subset_right hinj him g hg,
    measure_image_eq μ hFm inter_subset_right hinj him] at H
  exact H

end OAI.Geometry.Nikodym
