import OAI.RepresentationTheory.Weil.AdelicSplitting.UnramifiedAnnihilator
import OAI.RepresentationTheory.Weil.AdelicSplitting.SelfDualLattice
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanFourierCovers
import OAI.RepresentationTheory.Weil.AdelicSplitting.GraphReduction

/-! # Rational Fourier -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.RationalFourier.Construction

noncomputable section

/-! The prescribed restricted adelic Fourier family. Vacuum preservation
is a consequence of the normalized local unitary splittings and the exact
local Fourier formulas. No rational operator relation is assumed. -/

open Filter _root_.MeasureTheory
open scoped _root_.NumberField

open OAI.RepresentationTheory.Weil.AdelicSplitting.SelfDualLattice.LocalAnalysis

local instance e26RationalFourierMeasurable (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) :=
  borel (v.adicCompletion F)
local instance e26RationalFourierBorel (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

def finiteLatticeOpen (F : Type) [Field F] [NumberField F] (N : ℕ)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : OpenAddSubgroup (Local.FunctionsMetaplectic.Construction.Position (v.adicCompletion F) N) where
  __ := SelfDualLattice.LocalAnalysis.ringLatticeSubgroup (n := N) (Integral.Construction.localIntegerRing F (.inr v))
  isOpen' := (Vacuum.Construction.finitePositionLattice_clopen F N v).2

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0) (hds : ¬ IsSquare d)
  (n m : ℕ) (hN : 0 < n * m)
  (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
  (C : Characters.Construction.GlobalCharacters F d n m) (P : Assembly.Construction.GlobalFrames F d n m H K)
  (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)

include hds hH hK in
theorem normalizedLocalFourierOscillator_integral :
    ∀ᶠ v in cofinite,
      ArchimedeanFourierCovers.Construction.normalizedLocalFourierOscillator F d hd n m hN H K C P D v ∈ Vacuum.Construction.coverIntegral F (n * m) C.ψ v := by
  have hAnn := UnramifiedAnnihilator.Construction.normalized_local_annihilator_integer F d hd hds n m hN H K hH hK C P D
  have hchar := UnramifiedCharacter.Construction.eventually_cofinite_sum_right (I := NumberField.InfinitePlace F) _
    (UnramifiedCharacter.Construction.localAdditiveCharacter_unramified_finite F C.ψ C.ψ_unitary C.ψ_continuous)
  have hsym := Vacuum.Construction.rationalSymplecticLocal_integral F (n * m) (Local.Generators.Construction.weylSymplectic F (n * m))
  filter_upwards [hAnn, hchar, hsym] with v ha hc hs
  refine ⟨?_, ?_⟩
  · change Vacuum.Construction.projectionAt F (n * m) C.ψ v
      (ArchimedeanFourierCovers.Construction.normalizedLocalFourierOscillator F d hd n m hN H K C P D v) ∈ Vacuum.Construction.symplecticIntegral F (n * m) v
    rwa [ArchimedeanFourierCovers.Construction.normalizedLocalFourierOscillator_rational_covers]
  · cases v with
    | inl v => trivial
    | inr v =>
        let ψ := Characters.Construction.localAdditiveCharacter F C.ψ (.inr v)
        let μ := Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m) ψ
        let U := finiteLatticeOpen F (n * m) v
        let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v)) ψ).IsAddHaarMeasure :=
          NormalizationNonvanishing.Construction.normalized_selfDualMeasure_isAddHaarMeasure F d hd n m H K C P D (.inr v) hN
        let : μ.IsAddHaarMeasure := by unfold μ Local.FunctionsMetaplectic.Construction.positionMeasure; infer_instance
        have heq : CompactCharacter.LocalAnalysis.additiveAnnihilator ψ U.toAddSubgroup = U.toAddSubgroup :=
          SelfDualLattice.LocalAnalysis.ringLattice_annihilator_eq (Integral.Construction.localIntegerRing F (.inr v)) ψ hc ha
        have hF := SelfDualLattice.LocalAnalysis.selfDual_lattice_fourier_fixed ψ μ U (Vacuum.Construction.finitePositionLattice_compact F (n * m) v) heq
          (FiniteFourier.Construction.normalized_finite_fourier_inversion F d hd n m hN H K C P D v)
        change (ArchimedeanFourierCovers.Construction.normalizedLocalFourierOscillator F d hd n m hN H K C P D (.inr v)).val.2
          (Vacuum.Construction.finiteVacuum F (n * m) v) = Vacuum.Construction.finiteVacuum F (n * m) v
        apply Subtype.ext
        funext x
        change (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m) ψ
          (ArchimedeanFourierCovers.Construction.normalizedLocalFourierOscillator F d hd n m hN H K C P D (.inr v))
            (Vacuum.Construction.finiteVacuum F (n * m) v)).val x = _
        rw [ArchimedeanFourierCovers.Construction.normalizedLocalFourierOscillator_apply]
        exact congrFun hF.2 x

/-- The exact rational Weyl generator as a restricted family of actual
local oscillator operators. -/
def rationalFourierFamily : Rational.Construction.RestrictedCover F (n * m) C.ψ :=
  ⟨ArchimedeanFourierCovers.Construction.normalizedLocalFourierOscillator F d hd n m hN H K C P D,
    normalizedLocalFourierOscillator_integral F d hd hds n m hN H K hH hK C P D⟩

theorem rationalFourierFamily_spec :
    Rational.Construction.IsRationalFourier F (n * m) C.ψ (rationalFourierFamily F d hd hds n m hN H K hH hK C P D) :=
  ⟨ArchimedeanFourierCovers.Construction.normalizedLocalFourierOscillator_rational_covers F d hd n m hN H K C P D,
    ArchimedeanFourierCovers.Construction.normalizedLocalFourierOscillator_apply F d hd n m hN H K C P D⟩

def rationalFourierLift : Vacuum.Construction.GlobalCover F (n * m) C.ψ :=
  Rational.Construction.assembleGlobalCover F (n * m) C.ψ (rationalFourierFamily F d hd hds n m hN H K hH hK C P D)

theorem rationalFourierLift_mem_graph :
    (Local.Generators.Construction.weylSymplectic F (n * m), rationalFourierLift F d hd hds n m hN H K hH hK C P D) ∈
      Rational.Construction.rationalGraph F (n * m) C.ψ :=
  Subgroup.subset_closure (Or.inr (Or.inr
    ⟨rationalFourierFamily F d hd hds n m hN H K hH hK C P D,
      rationalFourierFamily_spec F d hd hds n m hN H K hH hK C P D, rfl⟩))

theorem rationalFourierLift_covers :
    Vacuum.Construction.globalProjection F (n * m) C.ψ (rationalFourierLift F d hd hds n m hN H K hH hK C P D) =
      Vacuum.Construction.rationalSymplectic F (n * m) (Local.Generators.Construction.weylSymplectic F (n * m)) :=
  Rational.Construction.assembled_covers_rational F (n * m) C.ψ _ _
    (rationalFourierFamily_spec F d hd hds n m hN H K hH hK C P D).1

include hds hH hK D hN in
theorem normalized_rationalGraph_total :
    ∀ γ : Local.FunctionsMetaplectic.Construction.Symplectic F (n * m), ∃ a, (γ, a) ∈ Rational.Construction.rationalGraph F (n * m) C.ψ :=
  GraphReduction.Construction.rationalGraph_total_of_fourier_family F (n * m) C.ψ C.ψ_unitary C.ψ_continuous
    ⟨rationalFourierFamily F d hd hds n m hN H K hH hK C P D,
      rationalFourierFamily_spec F d hd hds n m hN H K hH hK C P D⟩

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.RationalFourier.Construction
