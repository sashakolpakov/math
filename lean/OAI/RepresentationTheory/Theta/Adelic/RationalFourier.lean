import OAI.RepresentationTheory.Theta.Adelic.LocalFourier
import OAI.RepresentationTheory.Theta.Adelic.UnramifiedAnnihilator
import OAI.RepresentationTheory.Theta.Adelic.ExactFourier
import OAI.RepresentationTheory.Weil.AdelicSplitting.WeightedGaussianReciprocity

/-! # Rational Fourier -/

namespace OAI.RepresentationTheory.Theta.Adelic.RationalFourier

noncomputable section

/-! An exact restricted Fourier family and Gaussian reciprocity derived
from the global character alone, before local unitary splittings are built. -/

open Filter _root_.MeasureTheory
open scoped _root_.NumberField Classical

open OAI.RepresentationTheory.Weil.AdelicSplitting.WeightedGaussianReciprocity.Construction
open OAI.RepresentationTheory.Theta.Adelic.LocalFourier OAI.RepresentationTheory.Theta.Adelic.UnramifiedAnnihilator OAI.RepresentationTheory.Theta.Adelic.FiniteCharacterNontrivial

local instance (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) :=
  borel (v.adicCompletion F)
local instance (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

variable (F : Type) [Field F] [NumberField F]
variable (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ)
variable (hu : ∀ a, ‖ψ a‖ = 1) (hn : ∃ a, ψ a ≠ 1)
variable (hp : ∀ q : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q) = 1) (N : ℕ)

include hc hu hn hp

theorem localFourierOscillator_rational_covers (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :
    Weil.AdelicSplitting.Vacuum.Construction.projectionAt F N ψ v (LocalFourier.localFourierOscillator F ψ hc hu hn hp N v) =
      Weil.AdelicSplitting.Vacuum.Construction.rationalSymplecticLocal F N v (Weil.Local.Generators.Construction.weylSymplectic F N) := by
  rw [LocalFourier.localFourierOscillator_covers]
  apply Subtype.ext
  ext i j
  cases i <;> cases j <;>
    simp [Weil.AdelicSplitting.Vacuum.Construction.rationalSymplecticLocal, Weil.AdelicSplitting.Vacuum.Construction.mapSymplectic, Weil.Local.Generators.Construction.weylSymplectic_matrix,
      Matrix.fromBlocks, Matrix.map_apply, Matrix.one_apply]

theorem localFourierOscillator_integral :
    ∀ᶠ v in cofinite, LocalFourier.localFourierOscillator F ψ hc hu hn hp N v ∈ Weil.AdelicSplitting.Vacuum.Construction.coverIntegral F N ψ v := by
  have hAnn := UnramifiedAnnihilator.local_annihilator_integer F ψ hc hu hn hp
  have hchar := Weil.AdelicSplitting.UnramifiedCharacter.Construction.eventually_cofinite_sum_right (I := NumberField.InfinitePlace F) _
    (Weil.AdelicSplitting.UnramifiedCharacter.Construction.localAdditiveCharacter_unramified_finite F ψ hu hc)
  have hsym := Weil.AdelicSplitting.Vacuum.Construction.rationalSymplecticLocal_integral F N (Weil.Local.Generators.Construction.weylSymplectic F N)
  filter_upwards [hAnn, hchar, hsym] with v ha hc' hs
  refine ⟨?_, ?_⟩
  · change Weil.AdelicSplitting.Vacuum.Construction.projectionAt F N ψ v (LocalFourier.localFourierOscillator F ψ hc hu hn hp N v) ∈ Weil.AdelicSplitting.Vacuum.Construction.symplecticIntegral F N v
    rwa [localFourierOscillator_rational_covers]
  · cases v with
    | inl v => trivial
    | inr v =>
      let ψv := Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v)
      let μ := Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N ψv
      let U := Weil.AdelicSplitting.RationalFourier.Construction.finiteLatticeOpen F N v
      let : μ.IsAddHaarMeasure := LocalFourier.local_positionMeasure_isAddHaarMeasure F ψ hc hu hn hp N (.inr v)
      have heq : Weil.AdelicSplitting.CompactCharacter.LocalAnalysis.additiveAnnihilator ψv U.toAddSubgroup = U.toAddSubgroup :=
        Weil.AdelicSplitting.SelfDualLattice.LocalAnalysis.ringLattice_annihilator_eq (Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v)) ψv hc' ha
      have hF := Weil.AdelicSplitting.SelfDualLattice.LocalAnalysis.selfDual_lattice_fourier_fixed ψv μ U (Weil.AdelicSplitting.Vacuum.Construction.finitePositionLattice_compact F N v) heq
        (LocalFourier.local_fourier_inversion F ψ hc hu hn hp N (.inr v))
      apply Subtype.ext
      funext x
      exact congrFun hF.2 x

def rationalFourierFamily : Weil.AdelicSplitting.Rational.Construction.RestrictedCover F N ψ :=
  ⟨LocalFourier.localFourierOscillator F ψ hc hu hn hp N,
    localFourierOscillator_integral F ψ hc hu hn hp N⟩

theorem rationalFourierFamily_spec :
    Weil.AdelicSplitting.Rational.Construction.IsRationalFourier F N ψ (rationalFourierFamily F ψ hc hu hn hp N) :=
  ⟨localFourierOscillator_rational_covers F ψ hc hu hn hp N,
    LocalFourier.localFourierOscillator_apply F ψ hc hu hn hp N⟩

theorem localFourierOscillator_square_apply (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F)
    (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) N) (x : Weil.Local.FunctionsMetaplectic.Construction.Position (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) N) :
    (((LocalFourier.localFourierOscillator F ψ hc hu hn hp N v *
      LocalFourier.localFourierOscillator F ψ hc hu hn hp N v).val.2) f).val x = f.val (-x) := by
  let T := LocalFourier.localFourierOscillator F ψ hc hu hn hp N v
  have hT (g : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) N) : (T.val.2 g).val =
      Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ v)
        (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) N (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ v)) g.val :=
    funext (LocalFourier.localFourierOscillator_apply F ψ hc hu hn hp N v g)
  change (T.val.2 (T.val.2 f)).val x = _
  rw [hT, hT]
  exact LocalFourier.local_fourier_inversion F ψ hc hu hn hp N v f x

theorem localFourierOscillator_fourth (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :
    LocalFourier.localFourierOscillator F ψ hc hu hn hp N v ^ 4 = 1 := by
  let T := LocalFourier.localFourierOscillator F ψ hc hu hn hp N v
  apply Weil.AdelicSplitting.NormalizationLevi.Construction.localCover_ext
  · rw [map_pow, map_one]
    change Weil.AdelicSplitting.Vacuum.Construction.projectionAt F N ψ v T ^ 4 = 1
    rw [LocalFourier.localFourierOscillator_covers]
    exact Weil.AdelicSplitting.FourierRelations.Construction.weylSymplectic_fourth _ _
  · intro f x
    have hpow : T ^ 4 = (T * T) * (T * T) := by simp [pow_succ, mul_assoc]
    change ((T ^ 4).val.2 f).val x = f.val x
    rw [hpow]
    change ((T * T).val.2 ((T * T).val.2 f)).val x = _
    rw [localFourierOscillator_square_apply, localFourierOscillator_square_apply, neg_neg]

theorem rationalFourierFamily_fourth : rationalFourierFamily F ψ hc hu hn hp N ^ 4 = 1 := by
  apply RestrictedProduct.ext
  intro v
  exact localFourierOscillator_fourth F ψ hc hu hn hp N v

theorem theta_fourier (f : Weil.AdelicSplitting.RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    (f.act F N ψ (rationalFourierFamily F ψ hc hu hn hp N)).theta F N = f.theta F N :=
  ExactFourier.theta_fourier_exact F N ψ hc hu hp
    (fun v => FiniteCharacterNontrivial.local_character_nontrivial F ψ hc hu hn hp (.inl v))
    (fun v => LocalFourier.local_positionMeasure_isAddHaarMeasure F ψ hc hu hn hp N (.inr v))
    (fun v => LocalFourier.local_positionMeasure_isAddHaarMeasure F ψ hc hu hn hp N (.inl v))
    (rationalFourierFamily F ψ hc hu hn hp N) (rationalFourierFamily_spec F ψ hc hu hn hp N)
    (rationalFourierFamily_fourth F ψ hc hu hn hp N) f

theorem gaussianIndex_principal_hasProd (b : F) (hb : b ≠ 0) :
    HasProd (fun v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F => Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)
      (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ v) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v b)) 1 := by
  simpa only [pow_one] using Weil.AdelicSplitting.WeightedGaussianReciprocity.Construction.gaussianIndex_rational_power_hasProd F 1 ψ hc hu hp
    (FiniteCharacterNontrivial.local_character_nontrivial F ψ hc hu hn hp)
    (LocalFourier.local_positionMeasure_isAddHaarMeasure F ψ hc hu hn hp 1) b hb
    (rationalFourierFamily F ψ hc hu hn hp 1) (rationalFourierFamily_spec F ψ hc hu hn hp 1)

end

end OAI.RepresentationTheory.Theta.Adelic.RationalFourier
