import OAI.Geometry.Nikodym.Chart.Average

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Geometry.Nikodym


/-- The actual supremum of averages over a prescribed local tube family.
No measurability of an arbitrary uncountable family is built into this definition. -/
def chartTubeMaximal {n : ℕ} {ι : Type*} (ν : Measure (Space n))
    (T : Space n → ι → Set (Space n)) (admissible : Space n → ι → Prop)
    (f : Space n → ℂ) (x : Space n) : ℝ≥0∞ :=
  ⨆ i, ⨆ (_ : admissible x i), (∫⁻ y in T x i,‖f y‖ₑ ∂ν) / ν (T x i)

theorem chartTubeMaximal_le {n : ℕ} {ι : Type*} {ν : Measure (Space n)}
    {V : Set (Space n)} {a b : ℝ≥0∞} (ha : a≠⊤) (hb : b≠⊤)
    (hup : ν≤b • volume) (hdown : volume.restrict V≤a • ν)
    {r R l₀ : ℝ} (hr : 0<r) (hR : 1≤R) (hl₀ : 0<l₀)
    (T : Space n → ι → Set (Space n)) (admissible : Space n → ι → Prop)
    (hT : ∀ x i, admissible x i → ∃ l v c,
      l₀≤l ∧ l≤1 ∧ ‖v‖=1 ∧ x∈OAI.MeasureTheory.Kakeya.unitSegment (l•v) c ∧
      OAI.MeasureTheory.Kakeya.tube r (l•v) c⊆T x i ∧ OAI.MeasureTheory.Kakeya.tube r (l•v) c⊆V ∧ T x i⊆OAI.MeasureTheory.Kakeya.tube (R*r) v c)
    (f : Space n → ℂ) (x : Space n) :
    chartTubeMaximal ν T admissible f x ≤
      (a*b*ENNReal.ofReal (R^n*(l₀^n)⁻¹)) * nikodymMaximal (R*r) f x := by
  apply iSup_le
  intro i
  apply iSup_le
  intro hi
  obtain ⟨l,v,c,hl,hl1,hv,hx,hi,hV,ho⟩ := hT x i hi
  exact chartTube_average_le_nikodym ha hb hup hdown hr hR hl₀ hl hl1 hv hx hi hV ho f

/-- A bounded density change and a fixed tube distortion preserve the
Nikodym estimate. The output is a measurable majorant, so this theorem does
not incorrectly infer measurability for an arbitrary family of curves. -/
theorem nikodym_chart_majorant_bound (hN : NikodymMaximalConjecture)
    {n : ℕ} (hn : 2≤n) {ε : ℝ} (hε : 0<ε)
    {ν : Measure (Space n)} {V : Set (Space n)} (hV : MeasurableSet V)
    {a b : ℝ≥0∞} (ha : a≠⊤) (hb : b≠⊤)
    (hup : ν≤b • volume) (hdown : volume.restrict V≤a • ν)
    {R l₀ : ℝ} (hR : 1≤R) (_ : 0<l₀) :
    ∃ C : ℝ≥0∞, C<⊤ ∧ ∀ r : ℝ, 0<r → R*r≤1 →
      ∀ f : Space n → ℂ, MemLp f n ν → (∀ x∉V,f x=0) →
      let M := fun x => (a*b*ENNReal.ofReal (R^n*(l₀^n)⁻¹))*nikodymMaximal (R*r) f x
      Measurable M ∧ MemLp M n ν ∧
        eLpNorm M n ν ≤ C*ENNReal.ofReal (r^(-ε))*eLpNorm f n ν := by
  obtain ⟨K,hK,hKN⟩ := hN n hn ε hε
  let q : ℝ := (1/(n : ℝ≥0∞)).toReal
  let D : ℝ≥0∞ := a*b*ENNReal.ofReal (R^n*(l₀^n)⁻¹)
  let C : ℝ≥0∞ := D*b^q*ENNReal.ofReal K*a^q
  have haq : a^q≠⊤ := by simp [q,ha]
  have hbq : b^q≠⊤ := by simp [q,hb]
  have hD : D≠⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top ha hb) ENNReal.ofReal_ne_top
  have hC : C<⊤ := by
    apply Ne.lt_top
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hD hbq) ENNReal.ofReal_ne_top) haq
  refine ⟨C,hC,fun r hr hr1 f hf hfs => ?_⟩
  have hfvle : eLpNorm f n volume ≤ a^q*eLpNorm f n ν :=
    eLpNorm_le_of_comparable_measure_on hV f n hfs hdown
  have hfv : MemLp f n volume := hfvle.trans_lt (ENNReal.mul_lt_top haq.lt_top hf)
  have hRpos : 0<R := lt_of_lt_of_le zero_lt_one hR
  obtain ⟨hNm,hNb⟩ := hKN (R*r) (mul_pos hRpos hr) hr1 f hfv
  have hNmν : MemLp (nikodymMaximal (R*r) f) n ν := hNm.of_measure_le_smul hb hup
  have hMm : Measurable (fun x => D*nikodymMaximal (R*r) f x) :=
    (measurable_nikodymMaximal (R*r) f hfv.aestronglyMeasurable).const_mul D
  have hMle : eLpNorm (fun x => D*nikodymMaximal (R*r) f x) n ν ≤
      D*eLpNorm (nikodymMaximal (R*r) f) n ν := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' n hMm.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by simp
  refine ⟨hMm,hMle.trans_lt (ENNReal.mul_lt_top hD.lt_top hNmν),?_⟩
  have hpow : (R*r)^(-ε)≤r^(-ε) :=
    Real.rpow_le_rpow_of_nonpos hr (by nlinarith) (by linarith)
  calc
    _ ≤ D*eLpNorm (nikodymMaximal (R*r) f) n ν := hMle
    _ ≤ D*(b^q*eLpNorm (nikodymMaximal (R*r) f) n volume) :=
      mul_le_mul' le_rfl (eLpNorm_le_of_measure_le_smul hup)
    _ ≤ D*(b^q*(ENNReal.ofReal (K*(R*r)^(-ε))*eLpNorm f n volume)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl hNb)
    _ ≤ D*(b^q*(ENNReal.ofReal (K*r^(-ε))*(a^q*eLpNorm f n ν))) := by
      apply mul_le_mul' le_rfl
      apply mul_le_mul' le_rfl
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpow hK.le)) hfvle
    _ = _ := by
      rw [ENNReal.ofReal_mul hK.le]
      dsimp only [C]
      ac_rfl

/-- The local supremum itself satisfies the estimate as soon as the concrete
geodesic parametrization proves its measurability. All constants are chosen
before the tube family and the input function. -/
theorem nikodym_chart_family_bound (hN : NikodymMaximalConjecture)
    {n : ℕ} (hn : 2≤n) {ε : ℝ} (hε : 0<ε)
    {ν : Measure (Space n)} {V : Set (Space n)} (hV : MeasurableSet V)
    {a b : ℝ≥0∞} (ha : a≠⊤) (hb : b≠⊤)
    (hup : ν≤b • volume) (hdown : volume.restrict V≤a • ν)
    {R l₀ : ℝ} (hR : 1≤R) (hl₀ : 0<l₀) :
    ∃ C : ℝ, 0<C ∧ ∀ r : ℝ, 0<r → R*r≤1 →
      ∀ f : Space n → ℂ, MemLp f n ν → (∀ x∉V,f x=0) →
      ∀ (ι : Type*) (T : Space n → ι → Set (Space n)) (admissible : Space n → ι → Prop),
      (∀ x i, admissible x i → ∃ l v c,
        l₀≤l ∧ l≤1 ∧ ‖v‖=1 ∧ x∈OAI.MeasureTheory.Kakeya.unitSegment (l•v) c ∧
        OAI.MeasureTheory.Kakeya.tube r (l•v) c⊆T x i ∧ OAI.MeasureTheory.Kakeya.tube r (l•v) c⊆V ∧ T x i⊆OAI.MeasureTheory.Kakeya.tube (R*r) v c) →
      AEStronglyMeasurable (chartTubeMaximal ν T admissible f) ν →
      MemLp (chartTubeMaximal ν T admissible f) n ν ∧
      eLpNorm (chartTubeMaximal ν T admissible f) n ν ≤
        ENNReal.ofReal (C*r^(-ε))*eLpNorm f n ν := by
  obtain ⟨C,hC,hbound⟩ := nikodym_chart_majorant_bound hN hn hε hV ha hb hup hdown hR hl₀
  have hCp : 0<C.toReal+1 := by positivity
  refine ⟨C.toReal+1,hCp,fun r hr hr1 f hf hfs ι T admissible hT hm => ?_⟩
  obtain ⟨hMm,hM,hMb⟩ := hbound r hr hr1 f hf hfs
  have hdom := chartTubeMaximal_le ha hb hup hdown hr hR hl₀ T admissible hT f
  have hnorm := eLpNorm_mono_enorm
    (g := fun x => (a*b*ENNReal.ofReal (R^n*(l₀^n)⁻¹))*nikodymMaximal (R*r) f x)
    hm (fun x => by simpa using hdom x) (p := (n : ℝ≥0∞))
  have hcle : C≤ENNReal.ofReal (C.toReal+1) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal hC.ne]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  refine ⟨hnorm.trans_lt hM,?_⟩
  calc
    _ ≤ C*ENNReal.ofReal (r^(-ε))*eLpNorm f n ν := hnorm.trans hMb
    _ ≤ ENNReal.ofReal (C.toReal+1)*ENNReal.ofReal (r^(-ε))*eLpNorm f n ν := by
      exact mul_le_mul' (mul_le_mul' hcle le_rfl) le_rfl
    _ = _ := by rw [← ENNReal.ofReal_mul hCp.le]

end OAI.Geometry.Nikodym
