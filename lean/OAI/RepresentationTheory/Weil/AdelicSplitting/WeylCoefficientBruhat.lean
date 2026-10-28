import OAI.RepresentationTheory.Weil.AdelicSplitting.WeylCoefficientTransport
import OAI.RepresentationTheory.Weil.AdelicSplitting.ComplexWeylCoefficients
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealWeylCoefficients
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylSynthesisAdd
import OAI.RepresentationTheory.Weil.Local.ArchimedeanClassification

/-! # Weyl Coefficient Bruhat -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.WeylCoefficientBruhat.Construction

noncomputable section

/-! Actual Weyl matrix coefficients are Bruhat functions on doubled
position space at every nondiscrete local field. -/

open _root_.MeasureTheory

open OAI.RepresentationTheory.Weil.Local.ArchimedeanClassification.Construction

theorem positionWeylCoefficient_real_mem {N : ℕ}
    (ψ : AddChar ℝ ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ N)) [μ.IsAddHaarMeasure] (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ N) :
    WeylCoefficientTransport.Construction.positionWeylCoefficient ψ μ f.val h.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ (N + N) := by
  obtain ⟨Φ, hΦ⟩ := UnitarySplitting.RealWeylCoefficients.Construction.exists_real_weyl_coefficient_schwartz ψ hc hu hn μ f h
  refine ArchimedeanCharacters.LocalAnalysis.schwartzBruhat_archimedean_iff.mpr
    ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (PhaseMeasure.Construction.phaseCoordinates ℝ N).symm Φ, ?_⟩
  funext x
  exact (hΦ _).symm

theorem positionWeylCoefficient_complex_mem {N : ℕ}
    (ψ : AddChar ℂ ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position ℂ N)) [μ.IsAddHaarMeasure] (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℂ N) :
    WeylCoefficientTransport.Construction.positionWeylCoefficient ψ μ f.val h.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat ℂ (N + N) := by
  obtain ⟨Φ, hΦ⟩ := ComplexWeylCoefficients.Construction.exists_complex_weyl_coefficient_schwartz ψ hc hu hn μ f h
  let e : Local.FunctionsMetaplectic.Construction.Position ℂ (N + N) ≃L[ℝ] Local.FunctionsMetaplectic.Construction.PhaseSpace ℂ N :=
    { __ := (PhaseMeasure.Construction.phaseCoordinates ℂ N).symm.toLinearEquiv.restrictScalars ℝ
      continuous_toFun := (PhaseMeasure.Construction.phaseCoordinates ℂ N).symm.continuous
      continuous_invFun := (PhaseMeasure.Construction.phaseCoordinates ℂ N).continuous }
  refine ArchimedeanCharacters.LocalAnalysis.schwartzBruhat_archimedean_iff.mpr
    ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e Φ, ?_⟩
  funext x
  exact (hΦ _).symm

theorem positionWeylCoefficient_mem
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k] (hnd : ¬ DiscreteTopology k) {N : ℕ}
    (ψ : AddChar k ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k N)) [μ.IsAddHaarMeasure] (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    WeylCoefficientTransport.Construction.positionWeylCoefficient ψ μ f.val h.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k (N + N) := by
  let : SecondCountableTopology k := TestSpace.LocalAnalysis.localField_secondCountable k hnd
  by_cases hArch : ∀ m : ℕ, ‖(m : k)‖ ≤ 1
  · let : IsUltrametricDist k := IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one hArch
    exact Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem
      ((UnitarySplitting.UltraWeylCoefficients.Construction.weylMatrixCoefficient_locallyConstant_ultra hnd ψ hc μ f h).comp_continuous
        (PhaseMeasure.Construction.phaseCoordinates k N).symm.continuous)
      ((UnitarySplitting.WeylSynthesisAdd.Construction.weylMatrixCoefficient_compactSupport_ultra hnd ψ hn μ f h).comp_homeomorph
        (PhaseMeasure.Construction.phaseCoordinates k N).symm.toHomeomorph)
  · have hnt {l : Type} [Field l] (e : k ≃+* l) :
        ∃ t, (ψ.compAddMonoidHom e.symm.toAddMonoidHom) t ≠ 1 := by
      obtain ⟨x, hx⟩ := hn
      refine ⟨e x, ?_⟩
      change ψ (e.symm (e x)) ≠ 1
      rwa [e.symm_apply_apply]
    rcases Local.ArchimedeanClassification.Construction.localField_archimedean_classification k hArch with ⟨e, he, hi⟩ | ⟨e, he, hi⟩
    · exact WeylCoefficientTransport.Construction.positionWeylCoefficient_mem_fieldTransport e he hi ψ μ
        (fun ν _ f h => positionWeylCoefficient_real_mem _ (hc.comp hi) (fun t => hu _) (hnt e) ν f h) f h
    · exact WeylCoefficientTransport.Construction.positionWeylCoefficient_mem_fieldTransport e he hi ψ μ
        (fun ν _ f h => positionWeylCoefficient_complex_mem _ (hc.comp hi) (fun t => hu _) (hnt e) ν f h) f h

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.WeylCoefficientBruhat.Construction
