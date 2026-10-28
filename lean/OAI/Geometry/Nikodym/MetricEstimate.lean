import OAI.Geometry.Nikodym.MetricMaximal
import OAI.Geometry.Nikodym.Chart.Pullback

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Geometry.Nikodym


/-- Local Nikodym maximal estimates transport through a genuine bi-Lipschitz
chart with comparable volume. Geodesics may straighten to any segment length
in `[l₀,1]`. The tube-margin and measurability conditions are explicit geometric
obligations, not hidden in an abstract bounded-operator assumption. -/
theorem metricTubeMaximal_bound (hN : NikodymMaximalConjecture)
    {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    {n : ℕ} (hn : 2≤n) {ε : ℝ} (hε : 0<ε) (μ : Measure M)
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
    {l₀ : ℝ} (hl₀ : 0<l₀) :
    ∃ C : ℝ, 0<C ∧ ∀ δ : ℝ, 0<δ → (K:ℝ)*δ≤1 →
      ∀ (ι : Type*) (I : M → ι → Set M) (admissible : M → ι → Prop),
      (∀ x∈S,∀ i,admissible x i → I x i⊆S ∧ x∈I x i ∧
        ∃ l v c,l₀≤l ∧ l≤1 ∧ ‖v‖=1 ∧ F '' I x i=OAI.MeasureTheory.Kakeya.unitSegment (l•v) c ∧
          OAI.MeasureTheory.Kakeya.tube (δ/(L:ℝ)) (l•v) c⊆V) →
      ∀ f : M → ℂ, MemLp f n (μ.restrict S) →
      AEStronglyMeasurable (metricTubeMaximal μ S I admissible δ f) (μ.restrict S) →
      MemLp (metricTubeMaximal μ S I admissible δ f) n (μ.restrict S) ∧
      eLpNorm (metricTubeMaximal μ S I admissible δ f) n (μ.restrict S) ≤
        ENNReal.ofReal (C*δ^(-ε))*eLpNorm f n (μ.restrict S) := by
  have hLp : (0:ℝ)<L := lt_of_lt_of_le zero_lt_one hL
  have hR : (1:ℝ)≤(K:ℝ)*(L:ℝ) := by
    have hKr : (1:ℝ)≤K := hK
    have hLr : (1:ℝ)≤L := hL
    nlinarith
  obtain ⟨C,hC,hbound⟩ := nikodym_chart_pullback_bound hN hn hε (μ.restrict S) hFm
    hV ha hb hup hdown hR hLp hl₀
  refine ⟨C,hC,fun δ hδ hδ1 ι I admissible hI f hf hm => ?_⟩
  let f' : M → ℂ := hf.aestronglyMeasurable.mk f
  have hf'm : Measurable f' := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have heq : f =ᵐ[μ.restrict S] f' := hf.aestronglyMeasurable.ae_eq_mk
  let g : Space n → ℂ := V.indicator (f' ∘ G)
  have hgm : Measurable g := (hf'm.comp hGm).indicator hV
  have hgs : ∀ x∉V,g x=0 := fun x hx => indicator_of_notMem hx _
  have hg : g ∘ F =ᵐ[μ.restrict S] f := by
    filter_upwards [ae_restrict_mem hS,heq] with x hx hfx
    dsimp only [Function.comp_def]
    rw [show g (F x)=f' x from by
      simp only [g,indicator_of_mem (hmap hx),Function.comp_apply,hGF x hx]]
    exact hfx.symm
  have hgf : MemLp (g ∘ F) n (μ.restrict S) := hf.ae_eq hg.symm
  have hmaxeq := metricTubeMaximal_congr_ae hg I admissible δ
  have he : ((K:ℝ)*(L:ℝ))*(δ/(L:ℝ))=(K:ℝ)*δ := by field_simp
  have hdom : ∀ᵐ x ∂μ.restrict S,
      metricTubeMaximal μ S I admissible δ f x ≤
        (a*b*ENNReal.ofReal (((K:ℝ)*(L:ℝ))^n*(l₀^n)⁻¹))*
          nikodymMaximal (((K:ℝ)*(L:ℝ))*(δ/(L:ℝ))) g (F x) := by
    filter_upwards [ae_restrict_mem hS] with x hx
    rw [← hmaxeq,he]
    exact metricTubeMaximal_le_chart μ hS hV hFm hGm hK hL hF hG hmap hback hGF hFG
      ha hb hup hdown hδ hl₀ I admissible hI g hgm hx
  obtain ⟨hm',hb'⟩ := hbound δ hδ (by simpa only [he] using hδ1) g hgm hgf hgs
    (metricTubeMaximal μ S I admissible δ f) hm hdom
  refine ⟨hm',?_⟩
  simpa only [eLpNorm_congr_ae hg] using hb'

end OAI.Geometry.Nikodym
