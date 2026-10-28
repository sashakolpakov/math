import OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimeBoundedMatrix
import OAI.RepresentationTheory.Hecke.RadialDilation.FinitePrimePadic
import OAI.RepresentationTheory.Hecke.RadialDilation.FinitePhaseImage
import OAI.RepresentationTheory.Hecke.RadialDilation.FinitePrimeAssembly
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalTailTestPhase

/-! # Adelic Test Stabilization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdelicTestStabilization.Local

noncomputable section

/-! A rational finite tail and bounded local powers stabilize any actual finite-adelic test function up to an eighth root of unity. -/

open scoped Classical
open IsDedekindDomain

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem exists_adelic_power_test_phase
    (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition) (hI : 0 < Fintype.card I)
    (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ)
    (S : Finset (HeightOneSpectrum ℤ))
    (he : ∀ v ∉ S, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePrimeEval v) g =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePrimeEval v) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) γ))
    (hbounded : ∀ (q : ℕ) [Fact q.Prime], ∃ R : ℝ,
      ∀ (N : ℕ) i j, ‖((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom g) ^ N).val i j‖ ≤ R) :
    ∃ N : ℕ, 0 < N ∧ ∀ m : MpF, D.finite.project m = g ^ N →
      ∃ ξ : ℂ, ξ ^ 8 = 1 ∧ D.finite.action m f = ξ • f := by
  obtain ⟨T, _, htail⟩ := RationalTailTestPhase.Local.finite_tail_test_phase_of_rational_agreement D f g γ S he
  let H := RepresentationTheory.Hecke.RadialDilation.FinitePhaseImage.Realization.finiteEighthPhaseImage D f
  have hlocal (v : HeightOneSpectrum ℤ) (_hv : v ∈ T) :
      ∃ N : ℕ, 0 < N ∧ RepresentationTheory.Hecke.RadialDilation.FinitePrimeProduct.Realization.finitePrimePart g v ^ N ∈ H := by
    let q := (Rat.HeightOneSpectrum.primesEquiv v).val
    let : Fact q.Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
    have hvq : RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime q = v := RepresentationTheory.Hecke.RadialDilation.FinitePrimePadic.Realization.rationalPrime_of_place v
    let A := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom g
    obtain ⟨R, hR⟩ := hbounded q
    obtain ⟨m, hm⟩ := D.finite.surjective (RepresentationTheory.Hecke.RadialDilation.FinitePrimeProduct.Realization.finitePrimePart g v)
    have hmq : D.finite.project m = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q A :=
      hm.trans ((congrArg (RepresentationTheory.Hecke.RadialDilation.FinitePrimeProduct.Realization.finitePrimePart g) hvq).symm.trans (RepresentationTheory.Hecke.RadialDilation.FinitePrimePadic.Realization.finitePrimePart_padic q g))
    obtain ⟨N, ε, hN, hε, hf⟩ := RepresentationTheory.Hecke.RadialDilation.IndexedPrimeBoundedMatrix.Realization.exists_indexed_local_bounded_matrix_power_sign q (Fintype.equivFin I) hLocalWeil hI
      D A m hmq f R hR
    have hε8 : ε ^ 8 = 1 := by
      rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, hε, one_pow]
    have hmem := RepresentationTheory.Hecke.RadialDilation.FinitePhaseImage.Realization.finite_projection_mem_phase_image D f (m ^ N) ε hε8 hf
    rw [map_pow, hm] at hmem
    exact ⟨N, hN, hmem⟩
  obtain ⟨N, hN, hpower⟩ := RepresentationTheory.Hecke.RadialDilation.FinitePrimeAssembly.Realization.finite_prime_power_assembly H g T htail hlocal
  refine ⟨N, hN, ?_⟩
  intro m hm
  apply RepresentationTheory.Hecke.RadialDilation.FinitePhaseImage.Realization.finite_eighth_phase_of_projection_mem D f m
  rw [hm]
  exact hpower

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdelicTestStabilization.Local
