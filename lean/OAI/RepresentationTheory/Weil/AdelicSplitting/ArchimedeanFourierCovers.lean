import OAI.RepresentationTheory.Weil.AdelicSplitting.FourierTransport
import OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteFourier

/-! # Archimedean Fourier Covers -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanFourierCovers.Construction

noncomputable section

/-! The exact Fourier oscillator at every archimedean completion, obtained
by transporting the reference-set normalization from its real or complex model. -/

open _root_.MeasureTheory
open scoped _root_.NumberField

open OAI.RepresentationTheory.Weil.AdelicSplitting.FourierTransport.LocalAnalysis

local instance (F : Type) [Field F] [NumberField F] (v : NumberField.InfinitePlace F) :
    MeasurableSpace v.Completion := borel v.Completion
local instance (F : Type) [Field F] [NumberField F] (v : NumberField.InfinitePlace F) :
    BorelSpace v.Completion := ⟨rfl⟩
local instance (F : Type) [Field F] [NumberField F] (v : NumberField.InfinitePlace F) :
    CharZero v.Completion := ArchimedeanAdeles.Construction.completionCharZero F (.inl v)

local instance (F : Type) [Field F] [NumberField F] (v : NumberField.InfinitePlace F) :
    SecondCountableTopology v.Completion := by
  rcases v.isReal_or_isComplex with hv | hv
  · exact (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph.isEmbedding.secondCountableTopology
  · exact (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).toHomeomorph.isEmbedding.secondCountableTopology

theorem archimedean_fourier_analysis
    (F : Type) [Field F] [NumberField F] (N : ℕ) (v : NumberField.InfinitePlace F)
    (ψ : AddChar (ArchimedeanAdeles.Construction.Completion F (.inl v)) ℂ)
    (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1) :
    (∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F (.inl v)) N,
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inl v)) N ψ) f.val ∈
        Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F (.inl v)) N) ∧
    ∀ (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F (.inl v)) N) x,
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inl v)) N ψ)
        (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inl v)) N ψ) f.val) x = f.val (-x) := by
  rcases v.isReal_or_isComplex with hv | hv
  · let e := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv
    have he : Continuous e :=
      (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).continuous
    have hi : Continuous e.symm :=
      (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous
    let ψ' := ψ.compAddMonoidHom e.symm.toAddMonoidHom
    have hc' : Continuous ψ' := hc.comp hi
    have hu' : ∀ t, ‖ψ' t‖ = 1 := fun t => hu (e.symm t)
    have hn' : ∃ t, ψ' t ≠ 1 := by
      obtain ⟨x, hx⟩ := hn
      refine ⟨e x, ?_⟩
      change ψ (e.symm (e x)) ≠ 1
      rwa [e.symm_apply_apply]
    have h := RealNormalization.LocalAnalysis.real_fourier_analysis N ψ' hc' hu' hn'
    let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ').IsAddHaarMeasure :=
      FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℝ ψ' h.1
    have hm := FourierTransport.LocalAnalysis.selfDualMeasure_fieldTransport e he hi ψ (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ')
      (fun _ hS => ScalarPlancherel.LocalAnalysis.real_scalar_indicator_plancherel ψ' hc' hu' hn' hS)
    exact FourierTransport.LocalAnalysis.fourier_fieldTransport_analysis e he hi N ψ
      (Local.FunctionsMetaplectic.Construction.selfDualMeasure (ArchimedeanAdeles.Construction.Completion F (.inl v)) ψ) (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ') hm h.2.1 h.2.2
  · let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
    have he : Continuous e :=
      (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).continuous
    have hi : Continuous e.symm :=
      (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.continuous
    let ψ' := ψ.compAddMonoidHom e.symm.toAddMonoidHom
    have hc' : Continuous ψ' := hc.comp hi
    have hu' : ∀ t, ‖ψ' t‖ = 1 := fun t => hu (e.symm t)
    have hn' : ∃ t, ψ' t ≠ 1 := by
      obtain ⟨x, hx⟩ := hn
      refine ⟨e x, ?_⟩
      change ψ (e.symm (e x)) ≠ 1
      rwa [e.symm_apply_apply]
    have h := ComplexNormalization.LocalAnalysis.complex_fourier_analysis N ψ' hc' hu' hn'
    let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ').IsAddHaarMeasure :=
      FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℂ ψ' h.1
    have hm := FourierTransport.LocalAnalysis.selfDualMeasure_fieldTransport e he hi ψ (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ')
      (fun _ hS => ScalarPlancherel.LocalAnalysis.complex_scalar_indicator_plancherel ψ' hc' hu' hn' hS)
    exact FourierTransport.LocalAnalysis.fourier_fieldTransport_analysis e he hi N ψ
      (Local.FunctionsMetaplectic.Construction.selfDualMeasure (ArchimedeanAdeles.Construction.Completion F (.inl v)) ψ) (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ') hm h.2.1 h.2.2

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
  (n m : ℕ) (hN : 0 < n * m)
  (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (C : Characters.Construction.GlobalCharacters F d n m) (P : Assembly.Construction.GlobalFrames F d n m H K)
  (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)

/-- The archimedean raw Fourier operator, with the actual completion measure. -/
def normalizedArchimedeanFourierOscillator (v : NumberField.InfinitePlace F) :
    Vacuum.Construction.CoverAt F (n * m) C.ψ (.inl v) := by
  let ψ := Characters.Construction.localAdditiveCharacter F C.ψ (.inl v)
  have hu : ∀ t, ‖ψ t‖ = 1 := Characters.Construction.localAdditiveCharacter_unitary F C.ψ C.ψ_unitary (.inl v)
  have hc : Continuous ψ := Characters.Construction.localAdditiveCharacter_continuous F C.ψ C.ψ_continuous (.inl v)
  have hn := NontrivialLocalCharacter.Construction.normalizedLocalSplittings_character_nontrivial F d hd n m hN H K C P D (.inl v)
  have h := archimedean_fourier_analysis F (n * m) v ψ hc hu hn
  let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure (ArchimedeanAdeles.Construction.Completion F (.inl v)) ψ).IsAddHaarMeasure :=
    NormalizationNonvanishing.Construction.normalized_selfDualMeasure_isAddHaarMeasure F d hd n m H K C P D (.inl v) hN
  let : (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inl v)) (n * m) ψ).IsAddHaarMeasure := by
    unfold Local.FunctionsMetaplectic.Construction.positionMeasure
    infer_instance
  exact FourierIntertwiner.LocalAnalysis.fourierOscillator ψ hu hc (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inl v)) (n * m) ψ) h.1 h.2

theorem normalizedArchimedeanFourierOscillator_covers (v : NumberField.InfinitePlace F) :
    Vacuum.Construction.projectionAt F (n * m) C.ψ (.inl v)
      (normalizedArchimedeanFourierOscillator F d hd n m hN H K C P D v) =
      Local.Generators.Construction.weylSymplectic (ArchimedeanAdeles.Construction.Completion F (.inl v)) (n * m) := rfl

theorem normalizedArchimedeanFourierOscillator_apply (v : NumberField.InfinitePlace F)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F (.inl v)) (n * m)) (x : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inl v)) (n * m)) :
    (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F (.inl v)) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ (.inl v))
      (normalizedArchimedeanFourierOscillator F d hd n m hN H K C P D v) f).val x =
      Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F C.ψ (.inl v))
        (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inl v)) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ (.inl v)))
        f.val x := rfl

/-- The prescribed raw Fourier lift at every actual completion. -/
def normalizedLocalFourierOscillator (v : ArchimedeanAdeles.Construction.Places F) : Vacuum.Construction.CoverAt F (n * m) C.ψ v :=
  match v with
  | .inl v => normalizedArchimedeanFourierOscillator F d hd n m hN H K C P D v
  | .inr v => FiniteFourier.Construction.normalizedFiniteFourierOscillator F d hd n m hN H K C P D v

theorem normalizedLocalFourierOscillator_covers (v : ArchimedeanAdeles.Construction.Places F) :
    Vacuum.Construction.projectionAt F (n * m) C.ψ v
      (normalizedLocalFourierOscillator F d hd n m hN H K C P D v) =
      Local.Generators.Construction.weylSymplectic (ArchimedeanAdeles.Construction.Completion F v) (n * m) := by
  cases v <;> rfl

theorem normalizedLocalFourierOscillator_apply (v : ArchimedeanAdeles.Construction.Places F)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) (n * m)) (x : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F v) (n * m)) :
    (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v)
      (normalizedLocalFourierOscillator F d hd n m hN H K C P D v) f).val x =
      Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F C.ψ v)
        (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v)) f.val x := by
  cases v <;> rfl

theorem normalizedLocalFourierOscillator_rational_covers (v : ArchimedeanAdeles.Construction.Places F) :
    Vacuum.Construction.projectionAt F (n * m) C.ψ v
      (normalizedLocalFourierOscillator F d hd n m hN H K C P D v) =
      Vacuum.Construction.rationalSymplecticLocal F (n * m) v (Local.Generators.Construction.weylSymplectic F (n * m)) := by
  rw [normalizedLocalFourierOscillator_covers]
  apply Subtype.ext
  ext i j
  cases i <;> cases j <;>
    simp [Vacuum.Construction.rationalSymplecticLocal, Vacuum.Construction.mapSymplectic, Local.Generators.Construction.weylSymplectic_matrix,
      Matrix.fromBlocks, Matrix.map_apply, Matrix.one_apply]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanFourierCovers.Construction
