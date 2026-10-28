import OAI.RepresentationTheory.Theta.Adelic.FiniteCharacterNontrivial
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanFourierCovers

/-! # Local Fourier -/

namespace OAI.RepresentationTheory.Theta.Adelic.LocalFourier

noncomputable section

/-! The actual self-dual Haar measure and exact local Fourier operators
follow from the arithmetic character, without normalized local splittings. -/

open _root_.MeasureTheory
open scoped _root_.NumberField Classical

open OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanFourierCovers.Construction
open OAI.RepresentationTheory.Theta.Adelic.FiniteCharacterNontrivial

local instance (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) :=
  borel (v.adicCompletion F)
local instance (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

variable (F : Type) [Field F] [NumberField F]
variable (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ)
variable (hu : ∀ a, ‖ψ a‖ = 1) (hn : ∃ a, ψ a ≠ 1)
variable (hp : ∀ q : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q) = 1)

include hc hu hn hp

theorem local_fourier_inversion (N : ℕ) (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F)
    (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) N) (x : Weil.Local.FunctionsMetaplectic.Construction.Position (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) N) :
    Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ v)
      (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) N (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ v))
      (Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ v)
        (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) N (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ v)) f.val) x = f.val (-x) := by
  have hcv := Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_continuous F ψ hc v
  have huv := Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_unitary F ψ hu v
  have hnv := FiniteCharacterNontrivial.local_character_nontrivial F ψ hc hu hn hp v
  cases v with
  | inl v => exact (Weil.AdelicSplitting.ArchimedeanFourierCovers.Construction.archimedean_fourier_analysis F N v _ hcv huv hnv).2 f x
  | inr v => exact Weil.AdelicSplitting.NonarchimedeanNormalization.LocalAnalysis.nonarchimedean_fourier_inversion _ huv hcv hnv N f x

theorem local_selfDualMeasure_ne_zero (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :
    Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ v) ≠ 0 := by
  intro hzero
  obtain ⟨f, hf⟩ := Weil.AdelicSplitting.NontrivialLocalCharacter.Construction.local_test_one F 1 v
  have h := local_fourier_inversion F ψ hc hu hn hp 1 v f 0
  have hμ : Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) 1 (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ v) = 0 := by
    unfold Weil.Local.FunctionsMetaplectic.Construction.positionMeasure
    simp only [hzero]
    apply (Measure.measure_univ_eq_zero).mp
    rw [Measure.pi_univ]
    exact Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 1)) rfl
  rw [hμ, neg_zero, hf] at h
  simp only [Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral, integral_zero_measure, zero_ne_one] at h

theorem local_fourierHaarScaleSquared_pos (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :
    0 < Weil.Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ v) := by
  have h := local_selfDualMeasure_ne_zero F ψ hc hu hn hp v
  by_contra! hs
  apply h
  simp [Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure, Real.sqrt_eq_zero_of_nonpos hs]

theorem local_selfDualMeasure_isAddHaarMeasure (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :
    (Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ v)).IsAddHaarMeasure :=
  Weil.AdelicSplitting.FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos _ _
    (local_fourierHaarScaleSquared_pos F ψ hc hu hn hp v)

theorem local_positionMeasure_isAddHaarMeasure (N : ℕ) (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :
    (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) N (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ v)).IsAddHaarMeasure := by
  let : (Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ v)).IsAddHaarMeasure :=
    local_selfDualMeasure_isAddHaarMeasure F ψ hc hu hn hp v
  unfold Weil.Local.FunctionsMetaplectic.Construction.positionMeasure
  infer_instance

theorem local_fourier_mem (N : ℕ) (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F)
    (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) N) :
    Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ v)
      (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) N (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ v)) f.val ∈
        Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) N := by
  have hcv := Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_continuous F ψ hc v
  have huv := Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_unitary F ψ hu v
  have hnv := FiniteCharacterNontrivial.local_character_nontrivial F ψ hc hu hn hp v
  let : (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) N (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ v)).IsAddHaarMeasure :=
    local_positionMeasure_isAddHaarMeasure F ψ hc hu hn hp N v
  cases v with
  | inl v => exact (Weil.AdelicSplitting.ArchimedeanFourierCovers.Construction.archimedean_fourier_analysis F N v _ hcv huv hnv).1 f
  | inr v => exact Weil.AdelicSplitting.NonarchimedeanIntertwiner.LocalAnalysis.nonarchimedean_fourier_mem _ huv hcv hnv _ f

def localFourierOscillator (N : ℕ) (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) : Weil.AdelicSplitting.Vacuum.Construction.CoverAt F N ψ v := by
  let : (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) N (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ v)).IsAddHaarMeasure :=
    local_positionMeasure_isAddHaarMeasure F ψ hc hu hn hp N v
  exact Weil.AdelicSplitting.FourierIntertwiner.LocalAnalysis.fourierOscillator _ (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_unitary F ψ hu v)
    (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_continuous F ψ hc v) _
    (local_fourier_mem F ψ hc hu hn hp N v)
    (local_fourier_inversion F ψ hc hu hn hp N v)

theorem localFourierOscillator_covers (N : ℕ) (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :
    Weil.AdelicSplitting.Vacuum.Construction.projectionAt F N ψ v (localFourierOscillator F ψ hc hu hn hp N v) =
      Weil.Local.Generators.Construction.weylSymplectic (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) N := rfl

theorem localFourierOscillator_apply (N : ℕ) (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F)
    (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) N) (x : Weil.Local.FunctionsMetaplectic.Construction.Position (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) N) :
    (Weil.AdelicSplitting.Oscillator.Construction.localOperator (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) N (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ v)
      (localFourierOscillator F ψ hc hu hn hp N v) f).val x =
      Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ v)
        (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) N (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ v)) f.val x := rfl

end

end OAI.RepresentationTheory.Theta.Adelic.LocalFourier
