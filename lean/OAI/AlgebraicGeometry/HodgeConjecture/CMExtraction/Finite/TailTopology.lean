import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteMaskedGenerators
import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteQuadraticStabilization
import OAI.RepresentationTheory.Hecke.RadialDilation.FinitePhaseImage

/-! # Tail Topology -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.TailTopology.Local

noncomputable section

/-! Erasing a growing finite set of places sends every finite-adelic
coefficient to zero. Small upper unipotents therefore fix arbitrary
finite test functions up to the actual two-fold sign. -/

open scoped Classical _root_.Topology
open Filter IsDedekindDomain

theorem finite_tail_idempotent_tendsto :
    Tendsto (fun S : Finset (HeightOneSpectrum ℤ) =>
      RepresentationTheory.Hecke.RadialDilation.FiniteMaskedGenerators.Realization.finitePlaceIdempotent (S : Set (HeightOneSpectrum ℤ))ᶜ) atTop (𝓝 (0 : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) := by
  have h : Tendsto (fun S : Finset (HeightOneSpectrum ℤ) =>
      fun v : HeightOneSpectrum ℤ => if v ∈ (S : Set (HeightOneSpectrum ℤ))ᶜ then
        (1 : v.adicCompletionIntegers ℚ) else 0) atTop (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro v
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_finset_mem_atTop v] with S hS
    simp only [Set.mem_compl_iff, Finset.mem_coe, hS, not_true_eq_false, ite_false, Pi.zero_apply]
  have hc : Continuous (fun x => (RepresentationTheory.Theta.IntegralAdeles.PoissonAutomorphyConstruction.integralProductHomeomorph x).val) :=
    continuous_subtype_val.comp RepresentationTheory.Theta.IntegralAdeles.PoissonAutomorphyConstruction.integralProductHomeomorph.continuous
  have ht := (hc.tendsto 0).comp h
  convert ht using 1
  · funext S
    unfold RepresentationTheory.Hecke.RadialDilation.FiniteMaskedGenerators.Realization.finitePlaceIdempotent
    dsimp only [Function.comp_apply]
    apply congrArg (fun x => (RepresentationTheory.Theta.IntegralAdeles.PoissonAutomorphyConstruction.integralProductHomeomorph x).val)
    funext v
    split_ifs <;> rfl
  · rfl

theorem finite_tail_mask_tendsto (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    Tendsto (fun S : Finset (HeightOneSpectrum ℤ) =>
      RepresentationTheory.Hecke.RadialDilation.FiniteMaskedGenerators.Realization.finitePlaceMask (S : Set (HeightOneSpectrum ℤ))ᶜ a) atTop (𝓝 0) := by
  simpa only [zero_mul, RepresentationTheory.Hecke.RadialDilation.FiniteMaskedGenerators.Realization.finitePlaceMask] using finite_tail_idempotent_tendsto.mul_const a

theorem finite_tail_matrix_tendsto {I : Type*} (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    Tendsto (fun S : Finset (HeightOneSpectrum ℤ) =>
      RepresentationTheory.Hecke.RadialDilation.FiniteMaskedGenerators.Realization.finiteMaskCoefficients (S : Set (HeightOneSpectrum ℤ))ᶜ B) atTop (𝓝 0) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact finite_tail_mask_tendsto (B i j)

variable {I : Type*} [Fintype I] [DecidableEq I]
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA)

theorem eventually_finite_tail_upper_phase (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)
    (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) :
    ∀ᶠ S : Finset (HeightOneSpectrum ℤ) in atTop,
      RepresentationTheory.Hecke.RadialDilation.FiniteMaskedGenerators.Realization.finiteMaskSymplectic (S : Set (HeightOneSpectrum ℤ))ᶜ
        (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper B hB) ∈ RepresentationTheory.Hecke.RadialDilation.FinitePhaseImage.Realization.finiteEighthPhaseImage D f := by
  filter_upwards [(finite_tail_matrix_tendsto B).eventually (RepresentationTheory.Hecke.RadialDilation.FiniteQuadraticStabilization.Realization.eventually_finite_upper_sign D f)] with S hS
  rw [RepresentationTheory.Hecke.RadialDilation.FiniteMaskedGenerators.Realization.finiteMaskSymplectic_upper]
  obtain ⟨m, hm⟩ := D.finite.surjective
    (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper (RepresentationTheory.Hecke.RadialDilation.FiniteMaskedGenerators.Realization.finiteMaskCoefficients (S : Set (HeightOneSpectrum ℤ))ᶜ B)
      (RepresentationTheory.Hecke.RadialDilation.FiniteMaskedGenerators.Realization.finiteMaskCoefficients_symmetric _ B hB))
  obtain ⟨ε, hε, hf⟩ := hS _ m hm
  have he : ε ^ 8 = 1 := by
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, hε, one_pow]
  rw [← hm]
  exact RepresentationTheory.Hecke.RadialDilation.FinitePhaseImage.Realization.finite_projection_mem_phase_image D f m ε he hf

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.TailTopology.Local
