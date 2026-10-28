import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanPositionFourier
import OAI.RepresentationTheory.Weil.AdelicSplitting.CosetThetaPrimal
import OAI.RepresentationTheory.Weil.AdelicSplitting.CosetThetaDual
import OAI.RepresentationTheory.Weil.AdelicSplitting.CosetFourierExpansion
import OAI.RepresentationTheory.Weil.AdelicSplitting.RapidLatticePoisson

/-! # Theta Fourier Positive -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaFourierPositive.Construction

noncomputable section

/-! Adelic Poisson summation up to a positive scalar, derived for actual
restricted test families from finite cosets and real lattice Poisson. -/

open scoped Classical _root_.NumberField
open _root_.NumberField IsDedekindDomain _root_.MeasureTheory

open OAI.RepresentationTheory.Weil.AdelicSplitting.RapidLatticePoisson.LocalAnalysis

local instance thetaFourierFiniteMeasurable (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel (v.adicCompletion F)
local instance thetaFourierFiniteBorel (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
local instance thetaFourierInfiniteMeasurable (F : Type) [Field F]
    (v : InfinitePlace F) : MeasurableSpace v.Completion := borel v.Completion
local instance thetaFourierInfiniteBorel (F : Type) [Field F]
    (v : InfinitePlace F) : BorelSpace v.Completion := ⟨rfl⟩
local instance thetaFourierMixedBorel (F : Type) [Field F] [NumberField F] :
    BorelSpace (mixedEmbedding.mixedSpace F) := by
  unfold mixedEmbedding.mixedSpace
  infer_instance

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
variable (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1)
variable (hp : ∀ q : F, ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1)
variable (hn : ∀ v : InfinitePlace F, ∃ t : v.Completion, Characters.Construction.localAdditiveCharacter F ψ (.inl v) t ≠ 1)
variable (hμf : ∀ v : HeightOneSpectrum (𝓞 F),
  (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v)) N (Characters.Construction.localAdditiveCharacter F ψ (.inr v))).IsAddHaarMeasure)
variable (hμa : ∀ v : InfinitePlace F,
  (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inl v)) N (Characters.Construction.localAdditiveCharacter F ψ (.inl v))).IsAddHaarMeasure)

include hc hu hp hn hμf hμa in
theorem theta_fourier_cosets_positive (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalFourier F N ψ a)
    (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (M : ℕ) (hM : 0 < M) :
    ∃ c : ℝ, 0 < c ∧ ∀ b : Fin N → F,
      ((f.replaceFiniteByCoset F N (M : F) (by exact_mod_cast hM.ne') (FiniteCosets.Construction.finiteRationalPosition b)).act F N ψ a).theta F N =
        (c : ℂ) * (f.replaceFiniteByCoset F N (M : F) (by exact_mod_cast hM.ne') (FiniteCosets.Construction.finiteRationalPosition b)).theta F N := by
  obtain ⟨L, hL, hrat⟩ := ArchimedeanCharacterLattice.Construction.exists_archimedean_linear_character_rational F ψ hc hu hp
  have hsep := ArchimedeanDualLattice.Construction.archimedean_linear_pairing_separates F ψ hn L hL
  let μ := ArchimedeanPositionFourier.Construction.archimedeanPositionMeasure F N ψ
  let : μ.IsAddHaarMeasure := ArchimedeanPositionFourier.Construction.archimedeanPositionMeasure_isAddHaarMeasure F N ψ hμa
  let B := ArchimedeanPositionPairing.Construction.mixedPositionPairing F N L
  let b := MixedIntegerBasis.Construction.mixedIntegerPositionBasis F N M hM
  obtain ⟨V, hV, hVp⟩ := FiniteAnnihilator.Construction.finiteCosetVolume_hasProd F N ψ hμf a ha f (M : F) (by exact_mod_cast hM.ne')
  refine ⟨V * (LatticePoisson.LocalAnalysis.basisHaarFactor b μ : ℝ), mul_pos hV (by exact_mod_cast LatticePoisson.LocalAnalysis.basisHaarFactor_pos b μ), fun z => ?_⟩
  rw [f.theta_coset_dual_coordinates F N ψ hc hp hμf L hL hsep hrat a ha M hM z V hVp,
    f.theta_coset_primal_coordinates F N M hM z]
  have hP := RapidLatticePoisson.LocalAnalysis.rapid_lattice_poisson_shift_positive b B μ (ArchimedeanPositionPairing.Construction.mixedPositionPairing_separating F N L hsep)
    (f.mixedProductRapid F N) ((f.act F N ψ a).mixedProductRapid F N)
    (ArchimedeanPositionFourier.Construction.archimedean_fourier_product F N ψ hμa hc L hL a ha f) (ThetaTest.Construction.mixedRationalPosition F N z)
  have hsum : (∑' n : MixedIntegerBasis.Construction.MixedPositionIndex F N → ℤ,
      (f.act F N ψ a).mixedProductRapid F N (CosetThetaDual.Construction.mixedDualPosition F N L hsep M hM n) *
        RealCharacters.LocalAnalysis.realCharacter 1 (ArchimedeanPositionPairing.Construction.mixedPositionPairing F N L
          (CosetThetaDual.Construction.mixedDualPosition F N L hsep M hM n) (ThetaTest.Construction.mixedRationalPosition F N z))) =
      (LatticePoisson.LocalAnalysis.basisHaarFactor b μ : ℂ) * ∑' n : MixedIntegerBasis.Construction.MixedPositionIndex F N → ℤ,
        f.mixedProductRapid F N (ThetaTest.Construction.mixedRationalPosition F N z + b.equivFun.symm (fun p => (n p : ℝ))) := hP
  rw [hsum, Complex.ofReal_mul, mul_assoc]

include hc hu hp hn hμf hμa in
theorem theta_rational_fourier_positive (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalFourier F N ψ a)
    (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    ∃ c : ℝ, 0 < c ∧ (f.act F N ψ a).theta F N = (c : ℂ) * f.theta F N := by
  obtain ⟨M, hM, s, hs⟩ := f.finite_coset_expansion F N
  let g (j : s) := f.replaceFiniteByCoset F N (M : F) (by exact_mod_cast hM.ne')
    (FiniteCosets.Construction.finiteRationalPosition (FiniteCosets.Construction.finitePositionQuotientRep (M : F) (by exact_mod_cast hM.ne') j.val))
  let k (j : s) := f.finiteValue F N
    (FiniteCosets.Construction.finiteRationalPosition (FiniteCosets.Construction.finitePositionQuotientRep (M : F) (by exact_mod_cast hM.ne') j.val))
  have harch : ∀ j : s, ∀ v, g j (.inl v) = f (.inl v) := fun _ _ => rfl
  have hrel : ∀ x, f.finiteValue F N x = ∑ j : s, k j * (g j).finiteValue F N x := hs
  obtain ⟨c, hcp, hct⟩ := theta_fourier_cosets_positive F N ψ hc hu hp hn hμf hμa a ha f M hM
  refine ⟨c, hcp, ?_⟩
  rw [f.theta_fourier_of_finite_relation F N ψ hc hu hμf a ha g k harch hrel,
    f.theta_of_finite_relation F N g k harch hrel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj : ((g j).act F N ψ a).theta F N = (c : ℂ) * (g j).theta F N := hct _
  rw [hj]
  ring

include hc hu hp hn hμf hμa in
theorem rationalFourier_mem_positiveThetaSubgroup (a : Rational.Construction.RestrictedCover F N ψ)
    (ha : Rational.Construction.IsRationalFourier F N ψ a) : a ∈ TestFamilyAction.Construction.positiveThetaSubgroup F N ψ :=
  theta_rational_fourier_positive F N ψ hc hu hp hn hμf hμa a ha

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaFourierPositive.Construction
