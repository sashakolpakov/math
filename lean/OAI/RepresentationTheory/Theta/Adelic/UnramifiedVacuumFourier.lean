import OAI.RepresentationTheory.Theta.Adelic.RationalFourier
import OAI.RepresentationTheory.Weil.AdelicSplitting.WeylVacuum
import OAI.RepresentationTheory.Theta.Adelic.FieldWeylTransport

/-! # Unramified Vacuum Fourier -/

namespace OAI.RepresentationTheory.Theta.Adelic.UnramifiedVacuumFourier

noncomputable section

/-! Fourier normalization and exact volume of the standard finite
vacuum, obtained from the global additive character alone. -/

open _root_.MeasureTheory Filter
open scoped _root_.NumberField Classical ComplexConjugate NNReal

open OAI.RepresentationTheory.Weil.AdelicSplitting.WeylVacuum.Construction

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))

local instance : MeasurableSpace (v.adicCompletion F) := borel (v.adicCompletion F)
local instance : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

theorem vacuum_integral_of_fourier (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) ℂ)
    (μ : Measure (Weil.Local.FunctionsMetaplectic.Construction.Position (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N))
    (hF : Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val = (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val) :
    (∫ x, (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val x ∂μ) = 1 := by
  have h := congrFun hF 0
  simpa only [Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral, Weil.Local.FunctionsMetaplectic.Construction.dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    neg_zero, ψ.map_zero_eq_one, mul_one, Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum_zero] using h

theorem vacuum_pairing_energy :
    (∫ x, (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val x * conj ((Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val x)
      ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N) =
      (Weil.Local.FunctionsMetaplectic.Construction.l2Energy (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) : ℂ) := by
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact integral_ofReal

theorem vacuum_energy_haar_factor (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) ℂ)
    [(Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N ψ).IsAddHaarMeasure]
    (hF : Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N ψ)
      (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val = (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val) :
    (Weil.Local.FunctionsMetaplectic.Construction.l2Energy (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) : ℂ) =
      (Measure.addHaarScalarFactor
        (Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N)
        (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N ψ) : ℂ) := by
  rw [← vacuum_pairing_energy F N v]
  simp_rw [Weil.AdelicSplitting.WeylVacuum.Construction.finiteVacuum_mul_conj]
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul
      (Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N)
      (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N ψ)]
  rw [integral_smul_nnreal_measure, vacuum_integral_of_fourier F N v ψ _ hF]
  simp only [NNReal.smul_def, Complex.real_smul, mul_one]

theorem vacuum_reference_weyl_coefficient (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) ℂ)
    [(Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N ψ).IsAddHaarMeasure]
    (hF : Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N ψ)
      (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val = (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val)
    (hψ : ∀ t ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v), ψ t = 1)
    (hhalf : (2 : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v))⁻¹ ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v))
    (w : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N) :
    Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ
      (Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N)
      (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val w =
      (Weil.Local.FunctionsMetaplectic.Construction.l2Energy (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) : ℂ) *
        (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (N + N) v).val (Weil.AdelicSplitting.PhaseMeasure.Construction.phaseCoordinates (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N w) := by
  rw [vacuum_energy_haar_factor F N v ψ hF, Weil.AdelicSplitting.WeylVacuum.Construction.finiteVacuum_phaseCoordinates]
  unfold Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul
      (Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N)
      (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N ψ)]
  rw [integral_smul_nnreal_measure]
  change _ * Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ _ _ _ w = _
  rw [Weil.AdelicSplitting.WeylVacuum.Construction.finiteVacuum_weyl_coefficient F N v ψ _ hF hψ hhalf]
  rfl

variable (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ)
variable (hu : ∀ a, ‖ψ a‖ = 1) (hn : ∃ a, ψ a ≠ 1)
variable (hp : ∀ q : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q) = 1)

include hc hu hn hp in
theorem vacuum_fourier_fixed_eventually :
    ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) in cofinite,
      Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v))
        (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v)))
        (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val = (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val := by
  have ht : Tendsto (Sum.inr : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F)
      cofinite cofinite := Sum.inr_injective.tendsto_cofinite
  filter_upwards [ht.eventually
    (RationalFourier.localFourierOscillator_integral F ψ hc hu hn hp N)] with v hv
  have hf := hv.2
  apply funext
  intro x
  have he := congrArg (fun f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N => f.val x) hf
  exact (LocalFourier.localFourierOscillator_apply F ψ hc hu hn hp N (.inr v)
    (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) x).symm.trans he

end

end OAI.RepresentationTheory.Theta.Adelic.UnramifiedVacuumFourier
