import OAI.RepresentationTheory.Theta.Adelic.FieldWeylTransport
import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedWeakAnalysis
import OAI.RepresentationTheory.Weil.Local.ArchimedeanClassification
import OAI.RepresentationTheory.Weil.Local.Analytic

/-! # Local Weyl Integrability -/

namespace OAI.RepresentationTheory.Theta.Adelic.LocalWeylIntegrability

noncomputable section

/-! Absolute integrability of the actual Weyl coefficients and weak
Gaussian kernels over every characteristic-zero local field. -/

open _root_.MeasureTheory
open scoped NNReal

open OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedWeakAnalysis.Construction
open OAI.RepresentationTheory.Theta.Adelic.FieldWeylTransport

section Haar
variable {k : Type} [NormedField k] [LocallyCompactSpace k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}

theorem weyl_integrable_change_position (ψ : AddChar k ℂ)
    (μ : Measure (Weil.Local.FunctionsMetaplectic.Construction.Position k N)) [μ.IsAddHaarMeasure]
    (ν : Measure (Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N)) (f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N)
    (hi : Integrable (Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val h.val) ν) :
    Integrable (Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val h.val) ν := by
  let c := Measure.addHaarScalarFactor μ (Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N)
  have hm : μ = c • Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N := Measure.isAddLeftInvariant_eq_smul μ _
  have he (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N) : Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val h.val v =
      (c : ℂ) * Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val h.val v := by
    rw [Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient, hm, integral_smul_nnreal_measure]
    rfl
  convert hi.const_mul (c : ℂ) using 1
  funext v
  exact he v

end Haar

section Transport
variable {k l : Type} [NormedField k] [NormedField l] [LocallyCompactSpace k] [LocallyCompactSpace l]
variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace l] [BorelSpace l]
variable [SecondCountableTopology k] [SecondCountableTopology l] {N : ℕ}

omit [LocallyCompactSpace k] [LocallyCompactSpace l] in
theorem weyl_integrable_field (e : k ≃+* l) (he : Continuous e) (hi : Continuous e.symm)
    (ψ : AddChar k ℂ) (μ : Measure (Weil.Local.FunctionsMetaplectic.Construction.Position k N)) [μ.IsAddHaarMeasure]
    (ν : Measure (Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N)) [ν.IsAddHaarMeasure] (f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N)
    (hl : ∀ (μ' : Measure (Weil.Local.FunctionsMetaplectic.Construction.Position l N)) [μ'.IsAddHaarMeasure]
      (ν' : Measure (Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace l N)) [ν'.IsAddHaarMeasure] (f' h' : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat l N),
      Integrable (Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) μ' f'.val h'.val) ν') :
    Integrable (Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val h.val) ν := by
  let p := Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N
  let P := Weil.UnitarySplitting.FieldCoordinates.Construction.coordinateFieldEquiv (Fin N ⊕ Fin N) e he hi
  let : (μ.map p).IsAddHaarMeasure := p.isAddHaarMeasure_map μ
  let : (ν.map P).IsAddHaarMeasure := P.isAddHaarMeasure_map ν
  let f' := Weil.Local.FieldCoordinates.Construction.testSpaceTransport p f
  let h' := Weil.Local.FieldCoordinates.Construction.testSpaceTransport p h
  have ht := hl (μ.map p) (ν.map P) f' h'
  have hpull := (P.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integrable_map_iff).mp ht
  convert hpull using 1
  funext v
  exact (FieldWeylTransport.weylMatrixCoefficient_field e he hi N ψ μ f.val h.val v).symm

end Transport

theorem real_weyl_integrable (N : ℕ) (ψ : AddChar ℝ ℂ)
    (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (μ : Measure (Weil.Local.FunctionsMetaplectic.Construction.Position ℝ N)) [μ.IsAddHaarMeasure]
    (ν : Measure (Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ N)) [ν.IsAddHaarMeasure] (f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ N) :
    Integrable (Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val h.val) ν := by
  apply weyl_integrable_change_position ψ μ ν f h
  have hi := Weil.AdelicSplitting.CorrectedWeakAnalysis.Local.real_weak_phase_integrable N ψ hc hu hn ν
    (fun _ => 0) continuous_const f h
  simpa only [ψ.map_zero_eq_one, one_mul] using hi

theorem complex_weyl_integrable (N : ℕ) (ψ : AddChar ℂ ℂ)
    (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (μ : Measure (Weil.Local.FunctionsMetaplectic.Construction.Position ℂ N)) [μ.IsAddHaarMeasure]
    (ν : Measure (Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℂ N)) [ν.IsAddHaarMeasure] (f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℂ N) :
    Integrable (Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val h.val) ν := by
  apply weyl_integrable_change_position ψ μ ν f h
  have hi := Weil.AdelicSplitting.CorrectedWeakAnalysis.Local.complex_weak_phase_integrable N ψ hc hu hn ν
    (fun _ => 0) continuous_const f h
  simpa only [ψ.map_zero_eq_one, one_mul] using hi

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}

theorem local_weyl_integrable (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ)
    (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (μ : Measure (Weil.Local.FunctionsMetaplectic.Construction.Position k N)) [μ.IsAddHaarMeasure]
    (ν : Measure (Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N)) [ν.IsAddHaarMeasure] (f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    Integrable (Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val h.val) ν := by
  by_cases hArch : ∀ n : ℕ, ‖(n : k)‖ ≤ 1
  · let : IsUltrametricDist k :=
      IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one hArch
    exact (Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient_continuous ψ hc hu μ f h).integrable_of_hasCompactSupport
      (Weil.UnitarySplitting.WeylSynthesisAdd.Construction.weylMatrixCoefficient_compactSupport_ultra hnd ψ hn μ f h)
  · rcases Weil.Local.ArchimedeanClassification.Construction.localField_archimedean_classification k hArch with ⟨e, he, hei⟩ | ⟨e, he, hei⟩
    · exact weyl_integrable_field e he hei ψ μ ν f h
        (real_weyl_integrable N (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) (Weil.Local.ArchimedeanKernel.Construction.fieldCharacter_continuous e hei ψ hc)
          (Weil.Local.ArchimedeanKernel.Construction.fieldCharacter_unitary e ψ hu) (Weil.Local.ArchimedeanKernel.Construction.fieldCharacter_nontrivial e ψ hn))
    · exact weyl_integrable_field e he hei ψ μ ν f h
        (complex_weyl_integrable N (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) (Weil.Local.ArchimedeanKernel.Construction.fieldCharacter_continuous e hei ψ hc)
          (Weil.Local.ArchimedeanKernel.Construction.fieldCharacter_unitary e ψ hu) (Weil.Local.ArchimedeanKernel.Construction.fieldCharacter_nontrivial e ψ hn))

theorem local_weak_phase_integrable (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ)
    (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (μ : Measure (Weil.Local.FunctionsMetaplectic.Construction.Position k N)) [μ.IsAddHaarMeasure]
    (ν : Measure (Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N)) [ν.IsAddHaarMeasure]
    (Q : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N → k) (hQ : Continuous Q) (f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    Integrable (fun v => ψ (Q v) * Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val h.val v) ν := by
  apply (local_weyl_integrable hnd ψ hc hu hn μ ν f h).norm.mono'
    (((hc.comp hQ).mul (Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient_continuous ψ hc hu μ f h)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun v => by
    change ‖ψ (Q v) * Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val h.val v‖ ≤ _
    rw [norm_mul, hu, one_mul]

end

end OAI.RepresentationTheory.Theta.Adelic.LocalWeylIntegrability
