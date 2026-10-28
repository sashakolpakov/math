import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.TailTopology
import OAI.RepresentationTheory.Hecke.RadialDilation.RationalAgreementTail

/-! # Rational Tail Test Phase -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalTailTestPhase.Local

noncomputable section

/-! The rational finite tail has an eighth-root phase on every finite
test function. This is proved from small upper and lower unipotents,
without restricting the test function to the integral vacuum. -/

open scoped Classical
open Filter IsDedekindDomain
open OAI.RepresentationTheory.Hecke.RadialDilation.RationalAgreementTail.Realization

variable {I : Type*} [Fintype I] [DecidableEq I]
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA)

theorem finite_phase_image_conjugate (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (m : MpF) (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    (hg : g ∈ RepresentationTheory.Hecke.RadialDilation.FinitePhaseImage.Realization.finiteEighthPhaseImage D (D.finite.action m⁻¹ f)) :
    D.finite.project m * g * (D.finite.project m)⁻¹ ∈ RepresentationTheory.Hecke.RadialDilation.FinitePhaseImage.Realization.finiteEighthPhaseImage D f := by
  obtain ⟨v, ⟨ξ, hξ, hv⟩, he⟩ := hg
  refine ⟨m * v * m⁻¹, ⟨ξ, hξ, ?_⟩, ?_⟩
  · rw [map_mul, map_mul]
    change D.finite.action m (D.finite.action v (D.finite.action m⁻¹ f)) = ξ • f
    rw [hv, map_smul]
    congr 1
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  · rw [map_mul, map_mul, map_inv, he]

theorem eventually_finite_tail_lower_phase (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)
    (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) :
    ∀ᶠ S : Finset (HeightOneSpectrum ℤ) in atTop,
      RepresentationTheory.Hecke.RadialDilation.FiniteMaskedGenerators.Realization.finiteMaskSymplectic (S : Set (HeightOneSpectrum ℤ))ᶜ
        (RepresentationTheory.Hecke.RadialDilation.RingWeyl.Realization.ringLower RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf B hB) ∈ RepresentationTheory.Hecke.RadialDilation.FinitePhaseImage.Realization.finiteEighthPhaseImage D f := by
  obtain ⟨w, hw⟩ := D.finite.surjective (RepresentationTheory.Hecke.RadialDilation.RingWeyl.Realization.ringWeyl RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
  filter_upwards [Finite.TailTopology.Local.eventually_finite_tail_upper_phase D (D.finite.action w⁻¹ f) (-B) hB.neg] with S hS
  rw [RepresentationTheory.Hecke.RadialDilation.FiniteMaskedGenerators.Realization.finiteMaskSymplectic_upper] at hS
  have hneg : RepresentationTheory.Hecke.RadialDilation.FiniteMaskedGenerators.Realization.finiteMaskCoefficients (S : Set (HeightOneSpectrum ℤ))ᶜ (-B) =
      -RepresentationTheory.Hecke.RadialDilation.FiniteMaskedGenerators.Realization.finiteMaskCoefficients (S : Set (HeightOneSpectrum ℤ))ᶜ B := by
    ext i j
    exact mul_neg _ _
  simp only [hneg] at hS
  rw [RepresentationTheory.Hecke.RadialDilation.FiniteMaskedGenerators.Realization.finiteMaskSymplectic_lower, RepresentationTheory.Hecke.RadialDilation.RingWeyl.Realization.ringLower_conjugation]
  simpa only [hw] using finite_phase_image_conjugate D f w _ hS

def rationalTestTailSubgroup (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : Subgroup (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) where
  carrier := {γ | ∀ᶠ S : Finset (HeightOneSpectrum ℤ) in atTop,
    RepresentationTheory.Hecke.RadialDilation.FiniteMaskedGenerators.Realization.finiteMaskSymplectic (S : Set (HeightOneSpectrum ℤ))ᶜ
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) γ) ∈ RepresentationTheory.Hecke.RadialDilation.FinitePhaseImage.Realization.finiteEighthPhaseImage D f}
  one_mem' := by
    apply Filter.Eventually.of_forall
    intro S
    rw [map_one, map_one]
    exact Subgroup.one_mem _
  mul_mem' := by
    intro g h hg hh
    filter_upwards [hg, hh] with S hgS hhS
    rw [map_mul, map_mul]
    exact Subgroup.mul_mem _ hgS hhS
  inv_mem' := by
    intro g hg
    filter_upwards [hg] with S hgS
    rw [map_inv, map_inv]
    exact Subgroup.inv_mem _ hgS

theorem rationalTestTailSubgroup_eq_top (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : rationalTestTailSubgroup D f = ⊤ := by
  apply RepresentationTheory.Hecke.RadialDilation.RationalUnipotentGeneration.Realization.rationalSp_generated_by_unipotents
  · intro B hB
    change ∀ᶠ S : Finset (HeightOneSpectrum ℤ) in atTop,
      RepresentationTheory.Hecke.RadialDilation.FiniteMaskedGenerators.Realization.finiteMaskSymplectic (S : Set (HeightOneSpectrum ℤ))ᶜ
        (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper B hB)) ∈ _
    simp only [RepresentationTheory.Hecke.RadialDilation.FiniteMaskedGenerators.Realization.map_ringUpper]
    exact Finite.TailTopology.Local.eventually_finite_tail_upper_phase D f _ _
  · intro B hB
    change ∀ᶠ S : Finset (HeightOneSpectrum ℤ) in atTop,
      RepresentationTheory.Hecke.RadialDilation.FiniteMaskedGenerators.Realization.finiteMaskSymplectic (S : Set (HeightOneSpectrum ℤ))ᶜ
        (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (RepresentationTheory.Hecke.RadialDilation.RingWeyl.Realization.ringLower ℚ B hB)) ∈ _
    simp only [RepresentationTheory.Hecke.RadialDilation.FiniteMaskedGenerators.Realization.map_ringLower]
    exact eventually_finite_tail_lower_phase D f _ _

theorem rational_tail_test_phase (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) :
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ T : Finset (HeightOneSpectrum ℤ), S ⊆ T →
      RepresentationTheory.Hecke.RadialDilation.FiniteMaskedGenerators.Realization.finiteMaskSymplectic (T : Set (HeightOneSpectrum ℤ))ᶜ
        (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) γ) ∈ RepresentationTheory.Hecke.RadialDilation.FinitePhaseImage.Realization.finiteEighthPhaseImage D f := by
  have h : γ ∈ rationalTestTailSubgroup D f := by rw [rationalTestTailSubgroup_eq_top]; trivial
  exact h.exists_forall_of_atTop

theorem finite_tail_test_phase_of_rational_agreement (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)
    (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (S : Finset (HeightOneSpectrum ℤ))
    (he : ∀ v ∉ S, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePrimeEval v) g =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePrimeEval v) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) γ)) :
    ∃ T : Finset (HeightOneSpectrum ℤ), S ⊆ T ∧
      RepresentationTheory.Hecke.RadialDilation.FiniteMaskedGenerators.Realization.finiteMaskSymplectic (T : Set (HeightOneSpectrum ℤ))ᶜ g ∈ RepresentationTheory.Hecke.RadialDilation.FinitePhaseImage.Realization.finiteEighthPhaseImage D f := by
  obtain ⟨R, hR⟩ := rational_tail_test_phase D f γ
  refine ⟨S ∪ R, Finset.subset_union_left, ?_⟩
  rw [RepresentationTheory.Hecke.RadialDilation.RationalAgreementTail.Realization.finiteMask_agree_outside g _ S (S ∪ R) Finset.subset_union_left he]
  exact hR (S ∪ R) Finset.subset_union_right

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalTailTestPhase.Local
