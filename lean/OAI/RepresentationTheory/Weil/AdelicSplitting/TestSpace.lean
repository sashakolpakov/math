import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic

/-! # Test Space -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.TestSpace.LocalAnalysis

noncomputable section

/- AdelicSplitting-owned copy of the checked LocalWeil analytic helper development.
Kept in a separate namespace so this proof commit has no dependency on
another task's uncommitted modules. -/

/-! Analytic properties of the concrete Bruhat space used by LocalWeil. -/

open OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction

open _root_.MeasureTheory
open scoped ENNReal SchwartzMap

theorem localField_proper
    (k : Type) [NormedField k] [LocallyCompactSpace k]
    (h : ¬ DiscreteTopology k) : ProperSpace k := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField k with hd | ⟨_, rfl⟩
  · exact (h hd).elim
  · exact ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k

theorem localField_secondCountable
    (k : Type) [NormedField k] [LocallyCompactSpace k]
    (h : ¬ DiscreteTopology k) : SecondCountableTopology k := by
  let : ProperSpace k := localField_proper k h
  infer_instance

theorem schwartzBruhat_continuous
    {k : Type} [NormedField k] {n : ℕ}
    {f : Local.FunctionsMetaplectic.Construction.Position k n → ℂ} (hf : f ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) : Continuous f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with hf | ⟨d, e, φ, rfl⟩
      · exact hf.1.continuous
      · exact φ.continuous.comp e.symm.continuous
  | zero => exact continuous_const
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf => exact continuous_const.smul hf

theorem schwartzBruhat_memLp
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k] {n : ℕ}
    [SecondCountableTopology k]
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure] (p : ℝ≥0∞)
    {f : Local.FunctionsMetaplectic.Construction.Position k n → ℂ} (hf : f ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) : MemLp f p μ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with hf | ⟨d, e, φ, rfl⟩
      · exact hf.1.continuous.memLp_of_hasCompactSupport hf.2
      · let : (μ.map e.symm).IsAddHaarMeasure := e.symm.isAddHaarMeasure_map μ
        exact (φ.memLp p (μ.map e.symm)).comp_of_map
          e.symm.continuous.measurable.aemeasurable
  | zero => exact MemLp.zero
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf => exact hf.const_smul c

theorem schwartzBruhat_integrable
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k] {n : ℕ}
    [SecondCountableTopology k]
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) : Integrable f.val μ :=
  memLp_one_iff_integrable.mp (schwartzBruhat_memLp μ 1 f.property)

theorem schwartzBruhat_norm_sq_integrable
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k] {n : ℕ}
    [SecondCountableTopology k]
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) : Integrable (fun x => ‖f.val x‖ ^ 2) μ :=
  (schwartzBruhat_memLp μ 2 f.property).integrable_norm_pow (by decide)

theorem schwartzBruhat_integral_norm_sq_eq_zero_iff
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    (∫ x, ‖f.val x‖ ^ 2 ∂μ) = 0 ↔ f = 0 := by
  constructor
  · intro h
    have hae := (integral_eq_zero_iff_of_nonneg
      (fun x => sq_nonneg ‖f.val x‖) (schwartzBruhat_norm_sq_integrable μ f)).mp h
    have hf : f.val =ᵐ[μ] 0 := by
      filter_upwards [hae] with x hx
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)
    apply Subtype.ext
    exact Measure.eq_of_ae_eq hf (schwartzBruhat_continuous f.property) continuous_const
  · rintro rfl
    simp

theorem l2Energy_eq_zero_iff
    (k : Type) [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k]
    (h : ¬ DiscreteTopology k) (n : ℕ) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    Local.FunctionsMetaplectic.Construction.l2Energy k n f = 0 ↔ f = 0 := by
  let : SecondCountableTopology k := localField_secondCountable k h
  exact schwartzBruhat_integral_norm_sq_eq_zero_iff
    (Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure k))) f

/-- Additive coordinate changes preserve the actual test space. -/
theorem schwartzBruhat_comp_addEquiv
    {k : Type} [NormedField k] {m n : ℕ}
    (e : Local.FunctionsMetaplectic.Construction.Position k m ≃ₜ+ Local.FunctionsMetaplectic.Construction.Position k n)
    {f : Local.FunctionsMetaplectic.Construction.Position k n → ℂ} (hf : f ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    f ∘ e ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k m := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with hf | ⟨d, a, φ, rfl⟩
      · exact Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem
          (hf.1.comp_continuous e.continuous) (hf.2.comp_homeomorph e.toHomeomorph)
      · exact Local.FunctionsMetaplectic.Construction.schwartz_coordinate_mem (a.trans e.symm) φ
  | zero => exact (Local.FunctionsMetaplectic.Construction.schwartzBruhat k m).zero_mem
  | add f g _ _ hf hg => exact (Local.FunctionsMetaplectic.Construction.schwartzBruhat k m).add_mem hf hg
  | smul c f _ hf => exact (Local.FunctionsMetaplectic.Construction.schwartzBruhat k m).smul_mem c hf

def schwartzBruhat_coordinateEquiv
    {k : Type} [NormedField k] {m n : ℕ}
    (e : Local.FunctionsMetaplectic.Construction.Position k m ≃ₜ+ Local.FunctionsMetaplectic.Construction.Position k n) :
    Local.FunctionsMetaplectic.Construction.schwartzBruhat k n ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat k m where
  toFun f := ⟨f.val ∘ e, schwartzBruhat_comp_addEquiv e f.property⟩
  invFun f := ⟨f.val ∘ e.symm, schwartzBruhat_comp_addEquiv e.symm f.property⟩
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.TestSpace.LocalAnalysis
