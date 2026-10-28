import OAI.RepresentationTheory.Weil.AdelicSplitting.WeylCoefficientBruhat
import OAI.RepresentationTheory.Weil.AdelicSplitting.WeylVacuum

/-! # Weyl Families -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting

noncomputable section

/-! Restricted families of actual Weyl coefficients, using self-dual
position measure and the doubled unramified vacuum. -/

open _root_.MeasureTheory Filter IsDedekindDomain
open scoped Classical _root_.NumberField

local instance WeylFamilies.Construction.weylFamilyFiniteMeasurable (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel (v.adicCompletion F)
local instance WeylFamilies.Construction.weylFamilyFiniteBorel (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
variable (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
variable (hn : ∀ v : ArchimedeanAdeles.Construction.Places F, ∃ t : ArchimedeanAdeles.Construction.Completion F v, Characters.Construction.localAdditiveCharacter F ψ v t ≠ 1)
variable (hμ : ∀ v : ArchimedeanAdeles.Construction.Places F,
  (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)).IsAddHaarMeasure)
variable (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalFourier F N ψ a)

include hc hu a ha in
theorem WeylFamilies.Construction.fourier_family_vacuum_weyl :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      WeylCoefficientTransport.Construction.positionWeylCoefficient (Characters.Construction.localAdditiveCharacter F ψ (.inr v))
        (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v)) N (Characters.Construction.localAdditiveCharacter F ψ (.inr v)))
        (Vacuum.Construction.finiteVacuum F N v).val (Vacuum.Construction.finiteVacuum F N v).val = (Vacuum.Construction.finiteVacuum F (N + N) v).val := by
  have haint := Sum.inr_injective.tendsto_cofinite.eventually a.property
  have hhalf := Sum.inr_injective.tendsto_cofinite.eventually (Integral.Construction.rationalScalar_integral F (2 : F)⁻¹)
  have hchar := UnramifiedCharacter.Construction.localAdditiveCharacter_unramified_finite F ψ hu hc
  filter_upwards [haint, hhalf, hchar] with v hav h2 hc
  have hF : Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F ψ (.inr v))
      (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v)) N (Characters.Construction.localAdditiveCharacter F ψ (.inr v)))
      (Vacuum.Construction.finiteVacuum F N v).val = (Vacuum.Construction.finiteVacuum F N v).val := by
    funext x
    rw [← ha.2 (.inr v), show Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F (.inr v)) N
      (Characters.Construction.localAdditiveCharacter F ψ (.inr v)) (a (.inr v)) (Vacuum.Construction.finiteVacuum F N v) = Vacuum.Construction.finiteVacuum F N v from hav.2]
  have hh : (2 : ArchimedeanAdeles.Construction.Completion F (.inr v))⁻¹ ∈ Integral.Construction.localIntegerRing F (.inr v) := by
    simpa only [map_inv₀, map_ofNat] using h2
  funext x
  rw [WeylCoefficientTransport.Construction.positionWeylCoefficient, WeylVacuum.Construction.finiteVacuum_weyl_coefficient F N v _ _ hF hc hh,
    ← WeylVacuum.Construction.finiteVacuum_phaseCoordinates F N v, (PhaseMeasure.Construction.phaseCoordinates (ArchimedeanAdeles.Construction.Completion F (.inr v)) N).apply_symm_apply]

def RestrictedTestFamilies.Construction.RestrictedTestFamily.weylCoefficients (f h : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) : RestrictedTestFamilies.Construction.RestrictedTestFamily F (N + N) where
  component v := by
    let := hμ v
    exact ⟨WeylCoefficientTransport.Construction.positionWeylCoefficient (Characters.Construction.localAdditiveCharacter F ψ v)
      (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)) (f v).val (h v).val,
      WeylCoefficientBruhat.Construction.positionWeylCoefficient_mem (LocalKernel.Construction.completion_nondiscrete F v) _
        (Characters.Construction.localAdditiveCharacter_continuous F ψ hc v) (Characters.Construction.localAdditiveCharacter_unitary F ψ hu v) (hn v) _ (f v) (h v)⟩
  unramified := by
    filter_upwards [f.unramified, h.unramified, WeylFamilies.Construction.fourier_family_vacuum_weyl F N ψ hc hu a ha] with v hf hh hw
    apply Subtype.ext
    change WeylCoefficientTransport.Construction.positionWeylCoefficient (Characters.Construction.localAdditiveCharacter F ψ (.inr v))
      (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v)) N (Characters.Construction.localAdditiveCharacter F ψ (.inr v)))
      (f (.inr v)).val (h (.inr v)).val = _
    rw [hf, hh]
    exact hw

end

end OAI.RepresentationTheory.Weil.AdelicSplitting
