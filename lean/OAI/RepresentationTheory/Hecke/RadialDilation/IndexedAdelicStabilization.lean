import OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimeBoundedMatrix
import OAI.RepresentationTheory.Hecke.RadialDilation.FinitePrimePadic
import OAI.RepresentationTheory.Hecke.RadialDilation.FinitePhaseImage
import OAI.RepresentationTheory.Hecke.RadialDilation.FinitePrimeAssembly
import OAI.RepresentationTheory.Hecke.RadialDilation.RationalAgreementTail

/-! # Indexed Adelic Stabilization -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.IndexedAdelicStabilization.Realization

noncomputable section

/-! A rational integral tail and bounded local powers produce an actual finite-adelic eigenphase. -/

open scoped Classical
open IsDedekindDomain

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem exists_indexed_adelic_power_vacuum_phase
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition) (hI : 0 < Fintype.card I)
    (D : Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA) (g : Theta.PoissonAutomorphyNormalizationData.Sp I Theta.PoissonAutomorphyNormalizationData.AQf) (γ : Theta.PoissonAutomorphyNormalizationData.Sp I ℚ)
    (S : Finset (HeightOneSpectrum ℤ))
    (he : ∀ v ∉ S, Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePrimeEval v) g =
      Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePrimeEval v) (Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf) γ))
    (hbounded : ∀ (q : ℕ) [Fact q.Prime], ∃ R : ℝ,
      ∀ (N : ℕ) i j, ‖((Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePadicProjection q).toRingHom g) ^ N).val i j‖ ≤ R) :
    ∃ N : ℕ, 0 < N ∧ ∀ m : MpF, D.finite.project m = g ^ N →
      ∃ ξ : ℂ, ξ ^ 8 = 1 ∧ D.finite.action m Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction = ξ • Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction := by
  obtain ⟨T, _, hT⟩ := RationalAgreementTail.Realization.finite_tail_of_rational_agreement g γ S he
  let H := FinitePhaseImage.Realization.finiteEighthPhaseImage D Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction
  have htail : FiniteMaskedGenerators.Realization.finiteMaskSymplectic (T : Set (HeightOneSpectrum ℤ))ᶜ g ∈ H :=
    FiniteIntegralGenerators.Realization.finite_integral_generators_phase_image D hT
  have hlocal (v : HeightOneSpectrum ℤ) (_hv : v ∈ T) :
      ∃ N : ℕ, 0 < N ∧ FinitePrimeProduct.Realization.finitePrimePart g v ^ N ∈ H := by
    let q := (Rat.HeightOneSpectrum.primesEquiv v).val
    let : Fact q.Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
    have hvq : FiniteSchur.Realization.rationalPrime q = v := FinitePrimePadic.Realization.rationalPrime_of_place v
    let A := Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePadicProjection q).toRingHom g
    obtain ⟨R, hR⟩ := hbounded q
    obtain ⟨m, hm⟩ := D.finite.surjective (FinitePrimeProduct.Realization.finitePrimePart g v)
    have hmq : D.finite.project m = FiniteConjugation.Realization.finitePadicSymplecticInclusion q A :=
      hm.trans ((congrArg (FinitePrimeProduct.Realization.finitePrimePart g) hvq).symm.trans (FinitePrimePadic.Realization.finitePrimePart_padic q g))
    obtain ⟨N, ε, hN, hε, hf⟩ := IndexedPrimeBoundedMatrix.Realization.exists_indexed_local_bounded_matrix_power_sign q (Fintype.equivFin I) hLocalWeil hI
      D A m hmq Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction R hR
    have hε8 : ε ^ 8 = 1 := by
      rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, hε, one_pow]
    have hmem := FinitePhaseImage.Realization.finite_projection_mem_phase_image D Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction (m ^ N) ε hε8 hf
    rw [map_pow, hm] at hmem
    exact ⟨N, hN, hmem⟩
  obtain ⟨N, hN, hpower⟩ := FinitePrimeAssembly.Realization.finite_prime_power_assembly H g T htail hlocal
  refine ⟨N, hN, ?_⟩
  intro m hm
  apply FinitePhaseImage.Realization.finite_eighth_phase_of_projection_mem D Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction m
  rw [hm]
  exact hpower

end

end OAI.RepresentationTheory.Hecke.RadialDilation.IndexedAdelicStabilization.Realization
