import OAI.Geometry.Nikodym.Chart.Maximal

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Geometry.Nikodym


/-- The analytic chart transport in original coordinates, with a measurable
majorant rather than an implicit measurability claim for arbitrary suprema. -/
theorem nikodym_chart_pullback_bound (hN : NikodymMaximalConjecture)
    {n : ℕ} (hn : 2≤n) {ε : ℝ} (hε : 0<ε)
    {M : Type*} [MeasurableSpace M] (μ : Measure M)
    {F : M → Space n} (hF : Measurable F)
    {V : Set (Space n)} (hV : MeasurableSet V)
    {a b : ℝ≥0∞} (ha : a≠⊤) (hb : b≠⊤)
    (hup : Measure.map F μ≤b • volume) (hdown : volume.restrict V≤a • Measure.map F μ)
    {R L l₀ : ℝ} (hR : 1≤R) (hL : 0<L) (hl₀ : 0<l₀) :
    ∃ C : ℝ, 0<C ∧ ∀ δ : ℝ, 0<δ → R*(δ/L)≤1 →
      ∀ g : Space n → ℂ, Measurable g → MemLp (g ∘ F) n μ → (∀ x∉V,g x=0) →
      ∀ H : M → ℝ≥0∞, AEStronglyMeasurable H μ →
      (∀ᵐ x ∂μ,H x≤(a*b*ENNReal.ofReal (R^n*(l₀^n)⁻¹))*
        nikodymMaximal (R*(δ/L)) g (F x)) →
      MemLp H n μ ∧ eLpNorm H n μ ≤ ENNReal.ofReal (C*δ^(-ε))*eLpNorm (g ∘ F) n μ := by
  obtain ⟨C,hC,hbound⟩ := nikodym_chart_majorant_bound hN hn hε hV ha hb hup hdown hR hl₀
  let C' : ℝ≥0∞ := C*ENNReal.ofReal (L^ε)
  have hC' : C'<⊤ := ENNReal.mul_lt_top hC ENNReal.ofReal_lt_top
  have hCp : 0<C'.toReal+1 := by positivity
  refine ⟨C'.toReal+1,hCp,fun δ hδ hδ1 g hgm hg hgs H hH hdom => ?_⟩
  have hgnorm : eLpNorm g n (Measure.map F μ)=eLpNorm (g ∘ F) n μ :=
    eLpNorm_map_measure hgm.aestronglyMeasurable hF.aemeasurable
  have hgg : MemLp g n (Measure.map F μ) := by
    change eLpNorm g n (Measure.map F μ)<⊤
    rw [hgnorm]
    exact hg
  obtain ⟨hMm,hM,hMb⟩ := hbound (δ/L) (div_pos hδ hL) hδ1 g hgg hgs
  let Q : Space n → ℝ≥0∞ := fun x =>
    (a*b*ENNReal.ofReal (R^n*(l₀^n)⁻¹))*nikodymMaximal (R*(δ/L)) g x
  have hQnorm : eLpNorm (Q ∘ F) n μ=eLpNorm Q n (Measure.map F μ) :=
    (eLpNorm_map_measure hMm.aestronglyMeasurable hF.aemeasurable).symm
  have hle : eLpNorm H n μ≤eLpNorm (Q ∘ F) n μ :=
    eLpNorm_mono_enorm_ae hH (by simpa [Q] using hdom)
  have hcle : C'≤ENNReal.ofReal (C'.toReal+1) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal hC'.ne]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hp : (δ/L)^(-ε)=L^ε*δ^(-ε) := by
    rw [Real.div_rpow hδ.le hL.le,Real.rpow_neg hL.le]
    simp only [div_inv_eq_mul,mul_comm]
  refine ⟨?_,?_⟩
  · apply hle.trans_lt
    rw [hQnorm]
    exact hM
  calc
    _ ≤ eLpNorm Q n (Measure.map F μ) := hle.trans_eq hQnorm
    _ ≤ C*ENNReal.ofReal ((δ/L)^(-ε))*eLpNorm g n (Measure.map F μ) := hMb
    _ = C'*ENNReal.ofReal (δ^(-ε))*eLpNorm (g ∘ F) n μ := by
      rw [hp,ENNReal.ofReal_mul (Real.rpow_nonneg hL.le ε),hgnorm]
      dsimp only [C']
      ac_rfl
    _ ≤ ENNReal.ofReal (C'.toReal+1)*ENNReal.ofReal (δ^(-ε))*eLpNorm (g ∘ F) n μ :=
      mul_le_mul' (mul_le_mul' hcle le_rfl) le_rfl
    _ = _ := by rw [← ENNReal.ofReal_mul hCp.le]

end OAI.Geometry.Nikodym
