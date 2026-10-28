import OAI.RepresentationTheory.Weil.UnitarySplitting.RealCharacter
import OAI.RepresentationTheory.Weil.UnitarySplitting.TestSpaceAnalysis

/-! # Real Chart Test Space -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.RealChartTestSpace.Construction

noncomputable section

/-! The Bruhat space in any real additive coordinate chart. -/

open scoped SchwartzMap ContDiff

theorem locallyConstant_real_contDiff {V W : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : V → W} (hf : IsLocallyConstant f) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact contDiffAt_const.congr_of_eventuallyEq (hf.eventually_eq x)

theorem schwartzBruhat_realChart_iff
    {F : Type} [NormedField F] {d r : ℕ}
    (e : (Fin r → ℝ) ≃ₜ+ Local.FunctionsMetaplectic.Construction.Position F d) {f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ} :
    f ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat F d ↔
      ∃ φ : SchwartzMap (Fin r → ℝ) ℂ, f = fun x => φ (e.symm x) := by
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
        rcases hf with hf | ⟨r', e', φ, rfl⟩
        · have hl : IsLocallyConstant (f ∘ e) := hf.1.comp_continuous e.continuous
          have hc : HasCompactSupport (f ∘ e) := hf.2.comp_homeomorph e.toHomeomorph
          refine ⟨hc.toSchwartzMap (locallyConstant_real_contDiff hl), ?_⟩
          funext x
          change f x = f (e (e.symm x))
          rw [e.apply_symm_apply]
        · let a := e.trans e'.symm
          let L := a.toAddEquiv.toRealLinearEquiv a.continuous a.symm.continuous
          refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L φ, ?_⟩
          funext x
          change φ (e'.symm x) = φ (e'.symm (e (e.symm x)))
          rw [e.apply_symm_apply]
    | zero => exact ⟨0, rfl⟩
    | add f g _ _ hf hg =>
        obtain ⟨φ, rfl⟩ := hf
        obtain ⟨χ, rfl⟩ := hg
        exact ⟨φ + χ, rfl⟩
    | smul c f _ hf =>
        obtain ⟨φ, rfl⟩ := hf
        exact ⟨c • φ, rfl⟩
  · rintro ⟨φ, rfl⟩
    exact Local.FunctionsMetaplectic.Construction.schwartz_coordinate_mem e φ

theorem realChart_character_mul_mem
    {F : Type} [NormedField F] {d r : ℕ}
    (e : (Fin r → ℝ) ≃ₜ+ Local.FunctionsMetaplectic.Construction.Position F d)
    (χ : AddChar (Local.FunctionsMetaplectic.Construction.Position F d) ℂ)
    (hχ : Continuous (fun x : Local.FunctionsMetaplectic.Construction.Position F d => χ x))
    (hunit : ∀ x, ‖χ x‖ = 1)
    {f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ} (hf : f ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    (fun x => χ x * f x) ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat F d := by
  obtain ⟨φ, rfl⟩ := (schwartzBruhat_realChart_iff e).mp hf
  let η : AddChar (Fin r → ℝ) ℂ := χ.compAddMonoidHom e.toAddEquiv.toAddMonoidHom
  have hη : Function.HasTemperateGrowth (fun x : Fin r → ℝ => η x) :=
    RealCharacter.Construction.continuous_unitary_coordinate_character_temperate η (hχ.comp e.continuous) (fun x => hunit _)
  let θ := SchwartzMap.smulLeftCLM ℂ (fun x : Fin r → ℝ => η x) φ
  apply (schwartzBruhat_realChart_iff e).mpr
  refine ⟨θ, ?_⟩
  funext x
  change χ x * φ (e.symm x) =
    (SchwartzMap.smulLeftCLM ℂ (fun x : Fin r → ℝ => η x) φ) (e.symm x)
  rw [SchwartzMap.smulLeftCLM_apply_apply hη]
  change χ x * φ (e.symm x) = χ (e (e.symm x)) * φ (e.symm x)
  rw [e.apply_symm_apply]

theorem schwartzBruhat_translate_mem
    {F : Type} [NormedField F] {d : ℕ} (q : Local.FunctionsMetaplectic.Construction.Position F d)
    {f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ} (hf : f ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    (fun x => f (x - q)) ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat F d := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with hf | ⟨r, e, φ, rfl⟩
      · exact Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem
          (hf.1.comp_continuous (continuous_id.sub continuous_const))
          (hf.2.comp_homeomorph (Homeomorph.subRight q))
      · have hh := Local.FunctionsMetaplectic.Construction.schwartz_coordinate_mem e (φ.compSubConstCLM ℂ (e.symm q))
        convert hh using 1
        funext x
        change φ (e.symm (x - q)) = φ (e.symm x - e.symm q)
        rw [map_sub]
  | zero => exact (Local.FunctionsMetaplectic.Construction.schwartzBruhat F d).zero_mem
  | add f g _ _ hf hg => exact (Local.FunctionsMetaplectic.Construction.schwartzBruhat F d).add_mem hf hg
  | smul c f _ hf => exact (Local.FunctionsMetaplectic.Construction.schwartzBruhat F d).smul_mem c hf

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.RealChartTestSpace.Construction
