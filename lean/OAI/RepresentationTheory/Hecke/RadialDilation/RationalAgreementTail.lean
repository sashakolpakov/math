import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteMaskCoordinates

/-! # Rational Agreement Tail -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.RationalAgreementTail.Realization

noncomputable section

/-! Changing finitely many prime components retains the rational integral-tail property. -/

open scoped Classical
open IsDedekindDomain

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finiteMask_agree_outside (g h : Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf) (S T : Finset (HeightOneSpectrum ℤ))
    (hST : S ⊆ T) (he : ∀ v ∉ S, Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePrimeEval v) g = Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePrimeEval v) h) :
    FiniteMaskedGenerators.Realization.finiteMaskSymplectic (T : Set (HeightOneSpectrum ℤ))ᶜ g =
      FiniteMaskedGenerators.Realization.finiteMaskSymplectic (T : Set (HeightOneSpectrum ℤ))ᶜ h := by
  apply FiniteMaskCoordinates.Realization.finiteSymplectic_ext
  intro v
  rw [FiniteMaskedGenerators.Realization.finiteMaskSymplectic_projection, FiniteMaskedGenerators.Realization.finiteMaskSymplectic_projection]
  by_cases hv : v ∈ T
  · simp [hv]
  · simp only [Set.mem_compl_iff, Finset.mem_coe, hv, not_false_eq_true, ite_true]
    exact he v (fun h => hv (hST h))

theorem finite_tail_of_rational_agreement (g : Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf) (γ : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ)
    (S : Finset (HeightOneSpectrum ℤ))
    (he : ∀ v ∉ S, Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePrimeEval v) g =
      Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePrimeEval v) (Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf) γ)) :
    ∃ T : Finset (HeightOneSpectrum ℤ), S ⊆ T ∧
      FiniteMaskedGenerators.Realization.finiteMaskSymplectic (T : Set (HeightOneSpectrum ℤ))ᶜ g ∈ FiniteIntegralGenerators.Realization.finiteIntegralGeneratorSubgroup := by
  obtain ⟨R, hR⟩ := FiniteMaskCoordinates.Realization.rational_finite_integral_tail γ
  refine ⟨S ∪ R, Finset.subset_union_left, ?_⟩
  rw [finiteMask_agree_outside g _ S (S ∪ R) Finset.subset_union_left he]
  exact hR (S ∪ R) Finset.subset_union_right

end

end OAI.RepresentationTheory.Hecke.RadialDilation.RationalAgreementTail.Realization
