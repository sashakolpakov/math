import OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaFourierPositive
import OAI.RepresentationTheory.Weil.AdelicSplitting.PositiveTestFamily

/-! # Uniform Poisson -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.UniformPoisson.Construction

noncomputable section

/-! A common finite lattice of periods gives a uniform positive Poisson
multiplier for all actual restricted test families with those periods. -/

open scoped Classical _root_.NumberField
open _root_.NumberField IsDedekindDomain _root_.MeasureTheory

open OAI.RepresentationTheory.Weil.AdelicSplitting.PositiveTestFamily.LocalAnalysis

local instance uniformPoissonFiniteMeasurable (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel (v.adicCompletion F)
local instance uniformPoissonFiniteBorel (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
local instance uniformPoissonInfiniteMeasurable (F : Type) [Field F]
    (v : InfinitePlace F) : MeasurableSpace v.Completion := borel v.Completion
local instance uniformPoissonInfiniteBorel (F : Type) [Field F]
    (v : InfinitePlace F) : BorelSpace v.Completion := ⟨rfl⟩
local instance uniformPoissonMixedBorel (F : Type) [Field F] [NumberField F] :
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
theorem theta_fourier_cosets_uniform (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalFourier F N ψ a)
    (M : ℕ) (hM : 0 < M) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N, ∀ b : Fin N → F,
      ((f.replaceFiniteByCoset F N (M : F) (by exact_mod_cast hM.ne') (FiniteCosets.Construction.finiteRationalPosition b)).act F N ψ a).theta F N =
        (c : ℂ) * (f.replaceFiniteByCoset F N (M : F) (by exact_mod_cast hM.ne') (FiniteCosets.Construction.finiteRationalPosition b)).theta F N := by
  obtain ⟨L, hL, hrat⟩ := ArchimedeanCharacterLattice.Construction.exists_archimedean_linear_character_rational F ψ hc hu hp
  have hsep := ArchimedeanDualLattice.Construction.archimedean_linear_pairing_separates F ψ hn L hL
  let μ := ArchimedeanPositionFourier.Construction.archimedeanPositionMeasure F N ψ
  let : μ.IsAddHaarMeasure := ArchimedeanPositionFourier.Construction.archimedeanPositionMeasure_isAddHaarMeasure F N ψ hμa
  let B := ArchimedeanPositionPairing.Construction.mixedPositionPairing F N L
  let b := MixedIntegerBasis.Construction.mixedIntegerPositionBasis F N M hM
  obtain ⟨f₀, _⟩ := PositiveTestFamily.Construction.exists_theta_nonzero F N
  obtain ⟨V, hV, hVp⟩ := FiniteAnnihilator.Construction.finiteCosetVolume_hasProd F N ψ hμf a ha f₀ (M : F) (by exact_mod_cast hM.ne')
  refine ⟨V * (LatticePoisson.LocalAnalysis.basisHaarFactor b μ : ℝ), mul_pos hV (by exact_mod_cast LatticePoisson.LocalAnalysis.basisHaarFactor_pos b μ), fun f z => ?_⟩
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
theorem theta_fourier_uniform_period (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalFourier F N ψ a)
    (M : ℕ) (hM : 0 < M) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N,
      (∀ u ∈ FiniteLattices.Construction.finiteAdelicPositionLattice (ι := Fin N) (M : F) (by exact_mod_cast hM.ne'),
        ∀ x, f.finiteValue F N (u + x) = f.finiteValue F N x) →
      (f.act F N ψ a).theta F N = (c : ℂ) * f.theta F N := by
  obtain ⟨c, hcpos, hct⟩ := theta_fourier_cosets_uniform F N ψ hc hu hp hn hμf hμa a ha M hM
  refine ⟨c, hcpos, fun f hperiod => ?_⟩
  let hm : (M : F) ≠ 0 := by exact_mod_cast hM.ne'
  obtain ⟨s, hs⟩ := FiniteCosets.Construction.finite_function_coset_expansion (f.finiteValue F N)
    (f.finiteValue_compactSupport F N) (M : F) hm hperiod
  let g (j : s) := f.replaceFiniteByCoset F N (M : F) hm
    (FiniteCosets.Construction.finiteRationalPosition (FiniteCosets.Construction.finitePositionQuotientRep (M : F) hm j.val))
  let k (j : s) := f.finiteValue F N
    (FiniteCosets.Construction.finiteRationalPosition (FiniteCosets.Construction.finitePositionQuotientRep (M : F) hm j.val))
  have harch : ∀ j : s, ∀ v, g j (.inl v) = f (.inl v) := fun _ _ => rfl
  have hrel : ∀ x, f.finiteValue F N x = ∑ j : s, k j * (g j).finiteValue F N x := by
    intro x
    simp only [g, RestrictedTestFamilies.Construction.RestrictedTestFamily.replaceFiniteByCoset_finiteValue]
    exact (hs x).trans (Finset.sum_coe_sort s _).symm
  rw [f.theta_fourier_of_finite_relation F N ψ hc hu hμf a ha g k harch hrel,
    f.theta_of_finite_relation F N g k harch hrel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj : ((g j).act F N ψ a).theta F N = (c : ℂ) * (g j).theta F N := hct f _
  rw [hj]
  ring

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.UniformPoisson.Construction
