import OAI.RepresentationTheory.Weil.AdelicSplitting.NormalizationNonvanishing
import OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanNormalization
import OAI.RepresentationTheory.Weil.AdelicSplitting.RationalLevi

/-! # Finite Fourier -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteFourier.Construction

noncomputable section

/-! The raw Fourier oscillator and exact self-dual inversion at every finite
completion, using character nontriviality forced by the supplied normalization. -/

open scoped _root_.NumberField

open OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanNormalization.LocalAnalysis

local instance (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) :=
  borel (v.adicCompletion F)

local instance (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

local instance (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : CharZero (v.adicCompletion F) :=
  ArchimedeanAdeles.Construction.completionCharZero F (.inr v)

theorem normalized_finite_fourier_mem
    (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
    (n m : ℕ) (hN : 0 < n * m)
    (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
    (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
    (C : Characters.Construction.GlobalCharacters F d n m) (P : Assembly.Construction.GlobalFrames F d n m H K)
    (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m)) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
      (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v)))
      f.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m) := by
  let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v))
      (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))).IsAddHaarMeasure :=
    NormalizationNonvanishing.Construction.normalized_selfDualMeasure_isAddHaarMeasure F d hd n m H K C P D (.inr v) hN
  let : (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m)
      (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))).IsAddHaarMeasure := by
    unfold Local.FunctionsMetaplectic.Construction.positionMeasure
    infer_instance
  exact NonarchimedeanIntertwiner.LocalAnalysis.nonarchimedean_fourier_mem _
    (Characters.Construction.localAdditiveCharacter_unitary F C.ψ C.ψ_unitary (.inr v))
    (Characters.Construction.localAdditiveCharacter_continuous F C.ψ C.ψ_continuous (.inr v))
    (NontrivialLocalCharacter.Construction.normalizedLocalSplittings_character_nontrivial F d hd n m hN H K C P D (.inr v)) _ f

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
  (n m : ℕ) (hN : 0 < n * m)
  (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (C : Characters.Construction.GlobalCharacters F d n m) (P : Assembly.Construction.GlobalFrames F d n m H K)
  (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))

include D hN in
theorem normalized_finite_fourier_inversion
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m)) (x : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m)) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
      (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v)))
      (Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
        (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v)))
        f.val) x = f.val (-x) :=
  NonarchimedeanNormalization.LocalAnalysis.nonarchimedean_fourier_inversion (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
    (Characters.Construction.localAdditiveCharacter_unitary F C.ψ C.ψ_unitary (.inr v))
    (Characters.Construction.localAdditiveCharacter_continuous F C.ψ C.ψ_continuous (.inr v))
    (NontrivialLocalCharacter.Construction.normalizedLocalSplittings_character_nontrivial F d hd n m hN H K C P D (.inr v)) (n * m) f x

def normalizedFiniteFourierOscillator : Vacuum.Construction.CoverAt F (n * m) C.ψ (.inr v) :=
  NonarchimedeanNormalization.LocalAnalysis.nonarchimedeanRawFourierOscillator (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
    (Characters.Construction.localAdditiveCharacter_unitary F C.ψ C.ψ_unitary (.inr v))
    (Characters.Construction.localAdditiveCharacter_continuous F C.ψ C.ψ_continuous (.inr v))
    (NontrivialLocalCharacter.Construction.normalizedLocalSplittings_character_nontrivial F d hd n m hN H K C P D (.inr v)) (n * m)

theorem normalizedFiniteFourierOscillator_covers :
    Vacuum.Construction.projectionAt F (n * m) C.ψ (.inr v)
      (normalizedFiniteFourierOscillator F d hd n m hN H K C P D v) =
        Local.Generators.Construction.weylSymplectic (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m) := rfl

theorem normalizedFiniteFourierOscillator_apply
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m)) (x : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m)) :
    (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
      (normalizedFiniteFourierOscillator F d hd n m hN H K C P D v) f).val x =
        Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
          (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v)))
          f.val x := rfl

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteFourier.Construction
