import OAI.RepresentationTheory.Weil.AdelicSplitting.RationalFourier

/-! # Any Rank Fourier -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.AnyRankFourier.Construction

noncomputable section

/-! The original local splitting hypotheses determine the scalar character
and its self-dual integral lattice. Hence the exact restricted Fourier
operator exists in every auxiliary rank. -/

open Filter _root_.MeasureTheory
open scoped _root_.NumberField

local instance anyRankFourierFiniteMeasurable (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) :=
  borel (v.adicCompletion F)
local instance anyRankFourierFiniteBorel (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
  (n m : ℕ) (hN : 0 < n * m)
  (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (C : Characters.Construction.GlobalCharacters F d n m) (P : Assembly.Construction.GlobalFrames F d n m H K)
  (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P) (R : ℕ)

include D hN in
theorem normalized_anyRank_fourier_analysis (v : ArchimedeanAdeles.Construction.Places F) :
    (∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) R,
      Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F C.ψ v)
        (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) R (Characters.Construction.localAdditiveCharacter F C.ψ v)) f.val ∈
          Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) R) ∧
    ∀ (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) R) x,
      Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F C.ψ v)
        (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) R (Characters.Construction.localAdditiveCharacter F C.ψ v))
        (Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F C.ψ v)
          (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) R (Characters.Construction.localAdditiveCharacter F C.ψ v)) f.val) x = f.val (-x) := by
  have hc := Characters.Construction.localAdditiveCharacter_continuous F C.ψ C.ψ_continuous v
  have hu := Characters.Construction.localAdditiveCharacter_unitary F C.ψ C.ψ_unitary v
  have hn := NontrivialLocalCharacter.Construction.normalizedLocalSplittings_character_nontrivial F d hd n m hN H K C P D v
  let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F C.ψ v)).IsAddHaarMeasure :=
    NormalizationNonvanishing.Construction.normalized_selfDualMeasure_isAddHaarMeasure F d hd n m H K C P D v hN
  let : (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) R (Characters.Construction.localAdditiveCharacter F C.ψ v)).IsAddHaarMeasure := by
    unfold Local.FunctionsMetaplectic.Construction.positionMeasure
    infer_instance
  cases v with
  | inl v => exact ArchimedeanFourierCovers.Construction.archimedean_fourier_analysis F R v _ hc hu hn
  | inr v => exact ⟨NonarchimedeanIntertwiner.LocalAnalysis.nonarchimedean_fourier_mem _ hu hc hn _,
      NonarchimedeanNormalization.LocalAnalysis.nonarchimedean_fourier_inversion _ hu hc hn R⟩

def normalizedAnyRankFourierOscillator (v : ArchimedeanAdeles.Construction.Places F) : Vacuum.Construction.CoverAt F R C.ψ v := by
  let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F C.ψ v)).IsAddHaarMeasure :=
    NormalizationNonvanishing.Construction.normalized_selfDualMeasure_isAddHaarMeasure F d hd n m H K C P D v hN
  let : (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) R (Characters.Construction.localAdditiveCharacter F C.ψ v)).IsAddHaarMeasure := by
    unfold Local.FunctionsMetaplectic.Construction.positionMeasure
    infer_instance
  let h := normalized_anyRank_fourier_analysis F d hd n m hN H K C P D R v
  exact FourierIntertwiner.LocalAnalysis.fourierOscillator _ (Characters.Construction.localAdditiveCharacter_unitary F C.ψ C.ψ_unitary v)
    (Characters.Construction.localAdditiveCharacter_continuous F C.ψ C.ψ_continuous v) _ h.1 h.2

theorem normalizedAnyRankFourierOscillator_covers (v : ArchimedeanAdeles.Construction.Places F) :
    Vacuum.Construction.projectionAt F R C.ψ v (normalizedAnyRankFourierOscillator F d hd n m hN H K C P D R v) =
      Local.Generators.Construction.weylSymplectic (ArchimedeanAdeles.Construction.Completion F v) R := rfl

theorem normalizedAnyRankFourierOscillator_apply (v : ArchimedeanAdeles.Construction.Places F)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) R) (x : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F v) R) :
    (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) R (Characters.Construction.localAdditiveCharacter F C.ψ v)
      (normalizedAnyRankFourierOscillator F d hd n m hN H K C P D R v) f).val x =
      Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F C.ψ v)
        (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) R (Characters.Construction.localAdditiveCharacter F C.ψ v)) f.val x := rfl

theorem normalizedAnyRankFourierOscillator_rational_covers (v : ArchimedeanAdeles.Construction.Places F) :
    Vacuum.Construction.projectionAt F R C.ψ v (normalizedAnyRankFourierOscillator F d hd n m hN H K C P D R v) =
      Vacuum.Construction.rationalSymplecticLocal F R v (Local.Generators.Construction.weylSymplectic F R) := by
  rw [normalizedAnyRankFourierOscillator_covers]
  apply Subtype.ext
  ext i j
  cases i <;> cases j <;>
    simp [Vacuum.Construction.rationalSymplecticLocal, Vacuum.Construction.mapSymplectic, Local.Generators.Construction.weylSymplectic_matrix,
      Matrix.fromBlocks, Matrix.map_apply, Matrix.one_apply]

theorem normalizedAnyRankFourierOscillator_integral (hds : ¬ IsSquare d)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val) :
    ∀ᶠ v in cofinite,
      normalizedAnyRankFourierOscillator F d hd n m hN H K C P D R v ∈ Vacuum.Construction.coverIntegral F R C.ψ v := by
  have hAnn := UnramifiedAnnihilator.Construction.normalized_local_annihilator_integer F d hd hds n m hN H K hH hK C P D
  have hchar := UnramifiedCharacter.Construction.eventually_cofinite_sum_right (I := NumberField.InfinitePlace F) _
    (UnramifiedCharacter.Construction.localAdditiveCharacter_unramified_finite F C.ψ C.ψ_unitary C.ψ_continuous)
  have hsym := Vacuum.Construction.rationalSymplecticLocal_integral F R (Local.Generators.Construction.weylSymplectic F R)
  filter_upwards [hAnn, hchar, hsym] with v ha hc hs
  refine ⟨?_, ?_⟩
  · change Vacuum.Construction.projectionAt F R C.ψ v
      (normalizedAnyRankFourierOscillator F d hd n m hN H K C P D R v) ∈ Vacuum.Construction.symplecticIntegral F R v
    rwa [normalizedAnyRankFourierOscillator_rational_covers]
  · cases v with
    | inl v => trivial
    | inr v =>
        let ψ := Characters.Construction.localAdditiveCharacter F C.ψ (.inr v)
        let μ := Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v)) R ψ
        let U := RationalFourier.Construction.finiteLatticeOpen F R v
        let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v)) ψ).IsAddHaarMeasure :=
          NormalizationNonvanishing.Construction.normalized_selfDualMeasure_isAddHaarMeasure F d hd n m H K C P D (.inr v) hN
        let : μ.IsAddHaarMeasure := by unfold μ Local.FunctionsMetaplectic.Construction.positionMeasure; infer_instance
        have heq : CompactCharacter.LocalAnalysis.additiveAnnihilator ψ U.toAddSubgroup = U.toAddSubgroup :=
          SelfDualLattice.LocalAnalysis.ringLattice_annihilator_eq (Integral.Construction.localIntegerRing F (.inr v)) ψ hc ha
        have hF := SelfDualLattice.LocalAnalysis.selfDual_lattice_fourier_fixed ψ μ U (Vacuum.Construction.finitePositionLattice_compact F R v) heq
          (normalized_anyRank_fourier_analysis F d hd n m hN H K C P D R (.inr v)).2
        apply Subtype.ext
        funext x
        exact congrFun hF.2 x

def anyRankRationalFourierFamily (hds : ¬ IsSquare d)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val) : Rational.Construction.RestrictedCover F R C.ψ :=
  ⟨normalizedAnyRankFourierOscillator F d hd n m hN H K C P D R,
    normalizedAnyRankFourierOscillator_integral F d hd n m hN H K C P D R hds hH hK⟩

theorem anyRankRationalFourierFamily_spec (hds : ¬ IsSquare d)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val) :
    Rational.Construction.IsRationalFourier F R C.ψ (anyRankRationalFourierFamily F d hd n m hN H K C P D R hds hH hK) :=
  ⟨normalizedAnyRankFourierOscillator_rational_covers F d hd n m hN H K C P D R,
    normalizedAnyRankFourierOscillator_apply F d hd n m hN H K C P D R⟩

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.AnyRankFourier.Construction
