import OAI.RepresentationTheory.Weil.AdelicSplitting.MixedIntegerBasis
import OAI.RepresentationTheory.Weil.AdelicSplitting.LatticeDualCoordinates
import OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteAnnihilator
import OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaTest

/-! # Coset Theta Dual -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Weil.AdelicSplitting.CosetThetaDual.Construction

/-! The dual lattice coordinate sum is bijectively indexed by the actual
rational positions in the finite annihilator. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

open OAI.RepresentationTheory.Weil.AdelicSplitting.LatticeDualCoordinates.LocalAnalysis

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
variable (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ)
variable (hp : ∀ q : F, ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1)
variable (L : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
variable (hL : ∀ x, ArchimedeanCharacterLattice.Construction.archimedeanCharacter F ψ x = RealCharacters.LocalAnalysis.realCharacter 1 (L x))
variable (hsep : ∀ x : mixedEmbedding.mixedSpace F, (∀ y, L (x * y) = 0) → x = 0)
variable (hrat : ∀ r : 𝓞 F, ∃ q : ℚ, (q : ℝ) = L (mixedEmbedding F (algebraMap (𝓞 F) F r)))
variable (M : ℕ) (hM : 0 < M)

def mixedDualPosition (n : MixedIntegerBasis.Construction.MixedPositionIndex F N → ℤ) : Fin N → mixedEmbedding.mixedSpace F :=
  (LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates (MixedIntegerBasis.Construction.mixedIntegerPositionBasis F N M hM) (ArchimedeanPositionPairing.Construction.mixedPositionPairing F N L)
    (ArchimedeanPositionPairing.Construction.mixedPositionPairing_separating F N L hsep)).symm (fun p => (n p : ℝ))

include hc hp hL hrat in
theorem mixedDualPosition_range_iff (x : Fin N → mixedEmbedding.mixedSpace F) :
    (∃ n : MixedIntegerBasis.Construction.MixedPositionIndex F N → ℤ, mixedDualPosition F N L hsep M hM n = x) ↔
      ∃ ξ : Fin N → F, ThetaTest.Construction.mixedRationalPosition F N ξ = x ∧
        FiniteCosets.Construction.finiteRationalPosition ξ ∈ FiniteAnnihilator.Construction.finiteCosetAnnihilator F N ψ (M : F) (by exact_mod_cast hM.ne') := by
  rw [show (∃ n, mixedDualPosition F N L hsep M hM n = x) ↔
      ∀ n : MixedIntegerBasis.Construction.MixedPositionIndex F N → ℤ, RealCharacters.LocalAnalysis.realCharacter 1
        (ArchimedeanPositionPairing.Construction.mixedPositionPairing F N L x ((MixedIntegerBasis.Construction.mixedIntegerPositionBasis F N M hM).equivFun.symm
          (fun p => (n p : ℝ)))) = 1 from LatticeDualCoordinates.LocalAnalysis.latticeDualInteger_iff _ _ _ x]
  simp_rw [MixedIntegerBasis.Construction.mixedIntegerPositionBasis_integer_symm]
  have hall : (∀ n : MixedIntegerBasis.Construction.MixedPositionIndex F N → ℤ, RealCharacters.LocalAnalysis.realCharacter 1
        (ArchimedeanPositionPairing.Construction.mixedPositionPairing F N L x (MixedFiniteDuality.Construction.mixedScalarIntegerPosition F N (M : F)
          ((MixedIntegerBasis.Construction.integerPositionCoordinates F N).symm n))) = 1) ↔
      ∀ r : Fin N → 𝓞 F, RealCharacters.LocalAnalysis.realCharacter 1
        (ArchimedeanPositionPairing.Construction.mixedPositionPairing F N L x (MixedFiniteDuality.Construction.mixedScalarIntegerPosition F N (M : F) r)) = 1 := by
    constructor
    · intro h r
      simpa only [(MixedIntegerBasis.Construction.integerPositionCoordinates F N).symm_apply_apply] using h (MixedIntegerBasis.Construction.integerPositionCoordinates F N r)
    · intro h n
      exact h _
  rw [hall]
  exact MixedFiniteDuality.Construction.mixed_scalar_integer_dual_iff F N ψ hc hp L hL hsep hrat (M : F) (by exact_mod_cast hM.ne') x

include hc hp hL hrat in
theorem mixedDualPosition_rational (n : MixedIntegerBasis.Construction.MixedPositionIndex F N → ℤ) :
    ∃ ξ : Fin N → F, ThetaTest.Construction.mixedRationalPosition F N ξ = mixedDualPosition F N L hsep M hM n ∧
      FiniteCosets.Construction.finiteRationalPosition ξ ∈ FiniteAnnihilator.Construction.finiteCosetAnnihilator F N ψ (M : F) (by exact_mod_cast hM.ne') :=
  (mixedDualPosition_range_iff F N ψ hc hp L hL hsep hrat M hM _).mp ⟨n, rfl⟩

def mixedDualRational (n : MixedIntegerBasis.Construction.MixedPositionIndex F N → ℤ) : Fin N → F :=
  (mixedDualPosition_rational F N ψ hc hp L hL hsep hrat M hM n).choose

theorem mixedDualRational_spec (n : MixedIntegerBasis.Construction.MixedPositionIndex F N → ℤ) :
    ThetaTest.Construction.mixedRationalPosition F N (mixedDualRational F N ψ hc hp L hL hsep hrat M hM n) =
        mixedDualPosition F N L hsep M hM n ∧
      FiniteCosets.Construction.finiteRationalPosition (mixedDualRational F N ψ hc hp L hL hsep hrat M hM n) ∈
        FiniteAnnihilator.Construction.finiteCosetAnnihilator F N ψ (M : F) (by exact_mod_cast hM.ne') :=
  (mixedDualPosition_rational F N ψ hc hp L hL hsep hrat M hM n).choose_spec

def mixedDualEquiv : (MixedIntegerBasis.Construction.MixedPositionIndex F N → ℤ) ≃
    {ξ : Fin N → F | FiniteCosets.Construction.finiteRationalPosition ξ ∈
      FiniteAnnihilator.Construction.finiteCosetAnnihilator F N ψ (M : F) (by exact_mod_cast hM.ne')} :=
  Equiv.ofBijective (fun n => ⟨mixedDualRational F N ψ hc hp L hL hsep hrat M hM n,
    (mixedDualRational_spec F N ψ hc hp L hL hsep hrat M hM n).2⟩) (by
      constructor
      · intro n m h
        apply LatticeDualCoordinates.LocalAnalysis.latticeDualInteger_injective (MixedIntegerBasis.Construction.mixedIntegerPositionBasis F N M hM)
          (ArchimedeanPositionPairing.Construction.mixedPositionPairing F N L) (ArchimedeanPositionPairing.Construction.mixedPositionPairing_separating F N L hsep)
        have hh := congrArg (fun ξ => ThetaTest.Construction.mixedRationalPosition F N ξ.val) h
        simpa only [(mixedDualRational_spec F N ψ hc hp L hL hsep hrat M hM _).1] using! hh
      · intro ξ
        obtain ⟨n, hn⟩ := (mixedDualPosition_range_iff F N ψ hc hp L hL hsep hrat M hM _).mpr
          ⟨ξ.val, rfl, ξ.property⟩
        refine ⟨n, Subtype.ext (ThetaTest.Construction.mixedRationalPosition_injective F N ?_)⟩
        exact (mixedDualRational_spec F N ψ hc hp L hL hsep hrat M hM n).1.trans hn)

theorem mixedDualEquiv_apply (n : MixedIntegerBasis.Construction.MixedPositionIndex F N → ℤ) :
    ThetaTest.Construction.mixedRationalPosition F N (mixedDualEquiv F N ψ hc hp L hL hsep hrat M hM n).val =
      mixedDualPosition F N L hsep M hM n :=
  (mixedDualRational_spec F N ψ hc hp L hL hsep hrat M hM n).1

end RepresentationTheory.Weil.AdelicSplitting.CosetThetaDual.Construction

namespace RepresentationTheory.Weil.AdelicSplitting

/-! The Fourier theta sum of a rational finite coset is its positive
finite volume times the shifted archimedean dual lattice sum. -/

open scoped Classical _root_.NumberField
open _root_.NumberField IsDedekindDomain _root_.MeasureTheory

open OAI.RepresentationTheory.Weil.AdelicSplitting.LatticeDualCoordinates.LocalAnalysis

local instance CosetThetaDual.Construction.cosetDualMeasurableSpace (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel (v.adicCompletion F)

local instance CosetThetaDual.Construction.cosetDualBorelSpace (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
variable (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ)
variable (hp : ∀ q : F, ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1)
variable (hμ : ∀ v : HeightOneSpectrum (𝓞 F),
  (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v)) N (Characters.Construction.localAdditiveCharacter F ψ (.inr v))).IsAddHaarMeasure)

include hc hp hμ in
theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.theta_coset_dual
    (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalFourier F N ψ a)
    (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (q : F) (hq : q ≠ 0) (b : Fin N → F) (V : ℝ)
    (hV : HasProd (fun v => (FiniteAnnihilator.Construction.finiteLocalCosetVolume F N ψ q hq v : ℂ)) (V : ℂ)) :
    ((f.replaceFiniteByCoset F N q hq (FiniteCosets.Construction.finiteRationalPosition b)).act F N ψ a).theta F N =
      (V : ℂ) * ∑' ξ : {ξ : Fin N → F | FiniteCosets.Construction.finiteRationalPosition ξ ∈ FiniteAnnihilator.Construction.finiteCosetAnnihilator F N ψ q hq},
        (f.act F N ψ a).mixedProductRapid F N (ThetaTest.Construction.mixedRationalPosition F N ξ.val) *
          ArchimedeanCharacterLattice.Construction.archimedeanCharacter F ψ (∑ i, mixedEmbedding F (ξ.val i) * mixedEmbedding F (b i)) := by
  let S : Set (Fin N → F) := {ξ | FiniteCosets.Construction.finiteRationalPosition ξ ∈ FiniteAnnihilator.Construction.finiteCosetAnnihilator F N ψ q hq}
  let T (ξ : Fin N → F) := (f.act F N ψ a).mixedProductRapid F N (ThetaTest.Construction.mixedRationalPosition F N ξ) *
    ArchimedeanCharacterLattice.Construction.archimedeanCharacter F ψ (∑ i, mixedEmbedding F (ξ i) * mixedEmbedding F (b i))
  have he (ξ : Fin N → F) :
      ((f.replaceFiniteByCoset F N q hq (FiniteCosets.Construction.finiteRationalPosition b)).act F N ψ a).value F N
        (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (ξ i)) = S.indicator (fun ξ => (V : ℂ) * T ξ) ξ := by
    rw [RestrictedTestFamilies.Construction.RestrictedTestFamily.value_rational_factorization,
      FiniteAnnihilator.Construction.finite_coset_fourier_value F N ψ hμ hc a ha f q hq V hV]
    by_cases hξ : ξ ∈ S
    · rw [ite_eq_left (show FiniteCosets.Construction.finiteRationalPosition ξ ∈ FiniteAnnihilator.Construction.finiteCosetAnnihilator F N ψ q hq from hξ),
        Set.indicator_of_mem hξ]
      change (f.act F N ψ a).mixedProductRapid F N (ThetaTest.Construction.mixedRationalPosition F N ξ) *
        ((V : ℂ) * FiniteCharacterProduct.Construction.finiteAdelicCharacter F ψ (-(∑ i, algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) (ξ i) *
          algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) (b i)))) = _
      rw [FiniteCharacterProduct.Construction.finite_rational_dot_phase F ψ hp]
      dsimp only [T]
      ring
    · rw [ite_eq_right (show FiniteCosets.Construction.finiteRationalPosition ξ ∉ FiniteAnnihilator.Construction.finiteCosetAnnihilator F N ψ q hq from hξ),
        Set.indicator_of_notMem hξ, mul_zero]
  change (∑' ξ : Fin N → F, _) = _
  simp_rw [he]
  rw [← tsum_subtype S, tsum_mul_left]

include hc hp hμ in
theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.theta_coset_dual_coordinates
    (L : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hL : ∀ x, ArchimedeanCharacterLattice.Construction.archimedeanCharacter F ψ x = RealCharacters.LocalAnalysis.realCharacter 1 (L x))
    (hsep : ∀ x : mixedEmbedding.mixedSpace F, (∀ y, L (x * y) = 0) → x = 0)
    (hrat : ∀ r : 𝓞 F, ∃ q : ℚ, (q : ℝ) = L (mixedEmbedding F (algebraMap (𝓞 F) F r)))
    (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalFourier F N ψ a)
    (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (M : ℕ) (hM : 0 < M) (b : Fin N → F) (V : ℝ)
    (hV : HasProd (fun v => (FiniteAnnihilator.Construction.finiteLocalCosetVolume F N ψ (M : F) (by exact_mod_cast hM.ne') v : ℂ)) (V : ℂ)) :
    ((f.replaceFiniteByCoset F N (M : F) (by exact_mod_cast hM.ne') (FiniteCosets.Construction.finiteRationalPosition b)).act F N ψ a).theta F N =
      (V : ℂ) * ∑' n : MixedIntegerBasis.Construction.MixedPositionIndex F N → ℤ,
        (f.act F N ψ a).mixedProductRapid F N (CosetThetaDual.Construction.mixedDualPosition F N L hsep M hM n) *
          RealCharacters.LocalAnalysis.realCharacter 1 (ArchimedeanPositionPairing.Construction.mixedPositionPairing F N L
            (CosetThetaDual.Construction.mixedDualPosition F N L hsep M hM n) (ThetaTest.Construction.mixedRationalPosition F N b)) := by
  rw [f.theta_coset_dual F N ψ hc hp hμ a ha _ _ b V hV]
  congr 1
  symm
  let e := CosetThetaDual.Construction.mixedDualEquiv F N ψ hc hp L hL hsep hrat M hM
  calc
    _ = ∑' n : MixedIntegerBasis.Construction.MixedPositionIndex F N → ℤ,
        (f.act F N ψ a).mixedProductRapid F N (ThetaTest.Construction.mixedRationalPosition F N (e n).val) *
          ArchimedeanCharacterLattice.Construction.archimedeanCharacter F ψ (∑ i, mixedEmbedding F ((e n).val i) * mixedEmbedding F (b i)) := by
      apply tsum_congr
      intro n
      rw [← CosetThetaDual.Construction.mixedDualEquiv_apply F N ψ hc hp L hL hsep hrat M hM n, hL]
      rfl
    _ = _ := by
      simpa only using! e.tsum_eq (fun ξ =>
        (f.act F N ψ a).mixedProductRapid F N (ThetaTest.Construction.mixedRationalPosition F N ξ.val) *
          ArchimedeanCharacterLattice.Construction.archimedeanCharacter F ψ (∑ i, mixedEmbedding F (ξ.val i) * mixedEmbedding F (b i)))

end RepresentationTheory.Weil.AdelicSplitting

end

end OAI
