import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteMaskedGenerators
import OAI.RepresentationTheory.Hecke.RadialDilation.RationalUnipotentGeneration

/-! # Finite Mask Coordinates -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FiniteMaskCoordinates.Realization

noncomputable section

section

/-! One finite exceptional set controls all powers of a rational symplectic matrix away from it. -/

open scoped Classical _root_.Matrix
open _root_.Matrix IsDedekindDomain

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rationalIntegralTailSubgroup : Subgroup (Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ) where
  carrier := {γ | ∃ S : Finset (HeightOneSpectrum ℤ),
    ∀ T : Finset (HeightOneSpectrum ℤ), S ⊆ T →
      FiniteMaskedGenerators.Realization.finiteMaskSymplectic (T : Set (HeightOneSpectrum ℤ))ᶜ (Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf) γ) ∈
        FiniteIntegralGenerators.Realization.finiteIntegralGeneratorSubgroup}
  one_mem' := by
    refine ⟨∅, ?_⟩
    intro T _
    rw [map_one, map_one]
    exact Subgroup.one_mem _
  mul_mem' := by
    rintro g h ⟨S, hS⟩ ⟨R, hR⟩
    refine ⟨S ∪ R, ?_⟩
    intro T hT
    rw [map_mul, map_mul]
    exact Subgroup.mul_mem _ (hS T (Finset.Subset.trans Finset.subset_union_left hT))
      (hR T (Finset.Subset.trans Finset.subset_union_right hT))
  inv_mem' := by
    rintro g ⟨S, hS⟩
    refine ⟨S, ?_⟩
    intro T hT
    rw [map_inv, map_inv]
    exact Subgroup.inv_mem _ (hS T hT)

theorem rationalIntegralTailSubgroup_eq_top : rationalIntegralTailSubgroup (ι := ι) = ⊤ := by
  apply RationalUnipotentGeneration.Realization.rationalSp_generated_by_unipotents
  · intro B hB
    obtain ⟨S, hS⟩ := FiniteMaskedGenerators.Realization.exists_finite_mask_integral_coefficients (B.map (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf))
    refine ⟨S, ?_⟩
    intro T hT
    rw [FiniteMaskedGenerators.Realization.map_ringUpper, FiniteMaskedGenerators.Realization.finiteMaskSymplectic_upper]
    exact FiniteIntegralGenerators.Realization.finiteIntegralGeneratorSubgroup_upper _ _ (hS T hT)
  · intro B hB
    obtain ⟨S, hS⟩ := FiniteMaskedGenerators.Realization.exists_finite_mask_integral_coefficients (B.map (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf))
    refine ⟨S, ?_⟩
    intro T hT
    rw [FiniteMaskedGenerators.Realization.map_ringLower, FiniteMaskedGenerators.Realization.finiteMaskSymplectic_lower]
    exact FiniteIntegralGenerators.Realization.finiteIntegralGeneratorSubgroup_lower _ _ (hS T hT)

theorem rational_finite_integral_tail (γ : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ) :
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ T : Finset (HeightOneSpectrum ℤ), S ⊆ T →
      FiniteMaskedGenerators.Realization.finiteMaskSymplectic (T : Set (HeightOneSpectrum ℤ))ᶜ (Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf) γ) ∈
        FiniteIntegralGenerators.Realization.finiteIntegralGeneratorSubgroup := by
  have h : γ ∈ rationalIntegralTailSubgroup := by rw [rationalIntegralTailSubgroup_eq_top]; trivial
  exact h

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem every_rational_tail_power_phase (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA) (γ : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ) :
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ T : Finset (HeightOneSpectrum ℤ), S ⊆ T →
      ∀ (N : ℕ) (m : MpF),
        D.finite.project m =
          FiniteMaskedGenerators.Realization.finiteMaskSymplectic (T : Set (HeightOneSpectrum ℤ))ᶜ (Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf) (γ ^ N)) →
        ∃ ξ : ℂ, ξ ^ 8 = 1 ∧ D.finite.action m Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction = ξ • Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction := by
  obtain ⟨S, hS⟩ := rational_finite_integral_tail γ
  refine ⟨S, ?_⟩
  intro T hT N m hm
  apply FiniteIntegralGenerators.Realization.every_finite_integral_generator_phase D m
  rw [hm, map_pow, map_pow]
  exact Subgroup.pow_mem _ (hS T hT) N

end

/-! A coordinate change at one prime does not alter the complementary rational integral tail. -/

open scoped Classical _root_.Matrix
open _root_.Matrix IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finiteSymplectic_ext {g h : Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf}
    (he : ∀ v : HeightOneSpectrum ℤ, Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePrimeEval v) g = Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePrimeEval v) h) :
    g = h := by
  apply Subtype.ext
  apply FiniteConjugation.Realization.finiteMatrix_ext
  intro v
  exact congrArg Subtype.val (he v)

theorem finitePrimeSymplecticInclusion_other (v w : HeightOneSpectrum ℤ) (hw : w ≠ v)
    (g : Theta.PoissonAutomorphyNormalizationData.Sp ι (v.adicCompletion ℚ)) :
    Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePrimeEval w) (FiniteConjugation.Realization.finitePrimeSymplecticInclusion v g) = 1 :=
  Subtype.ext (FiniteConjugation.Realization.finitePrimeMatrix_eval_other v w hw g.val)

theorem finiteMaskSymplectic_kills_prime (S : Set (HeightOneSpectrum ℤ))
    (v : HeightOneSpectrum ℤ) (hv : v ∉ S) (g : Theta.PoissonAutomorphyNormalizationData.Sp ι (v.adicCompletion ℚ)) :
    FiniteMaskedGenerators.Realization.finiteMaskSymplectic S (FiniteConjugation.Realization.finitePrimeSymplecticInclusion v g) = 1 := by
  apply finiteSymplectic_ext
  intro w
  rw [FiniteMaskedGenerators.Realization.finiteMaskSymplectic_projection, map_one]
  by_cases hw : w ∈ S
  · rw [ite_eq_left hw]
    exact finitePrimeSymplecticInclusion_other v w (fun h => hv (h ▸ hw)) g
  · rw [ite_eq_right hw]

theorem finiteMaskSymplectic_one_prime_conjugation (S : Set (HeightOneSpectrum ℤ))
    (v : HeightOneSpectrum ℤ) (hv : v ∉ S)
    (s : Theta.PoissonAutomorphyNormalizationData.Sp ι (v.adicCompletion ℚ)) (g : Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf) :
    FiniteMaskedGenerators.Realization.finiteMaskSymplectic S (FiniteConjugation.Realization.finitePrimeSymplecticInclusion v s * g *
      (FiniteConjugation.Realization.finitePrimeSymplecticInclusion v s)⁻¹) = FiniteMaskedGenerators.Realization.finiteMaskSymplectic S g := by
  rw [map_mul, map_mul, map_inv, finiteMaskSymplectic_kills_prime S v hv,
    one_mul, inv_one, mul_one]

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem every_conjugated_rational_tail_power_phase (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (γ : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ) (v : HeightOneSpectrum ℤ) (s : Theta.PoissonAutomorphyNormalizationData.Sp ι (v.adicCompletion ℚ)) :
    ∃ S : Finset (HeightOneSpectrum ℤ), v ∈ S ∧
      ∀ T : Finset (HeightOneSpectrum ℤ), S ⊆ T → ∀ (N : ℕ) (m : MpF),
        D.finite.project m = FiniteMaskedGenerators.Realization.finiteMaskSymplectic (T : Set (HeightOneSpectrum ℤ))ᶜ
          (FiniteConjugation.Realization.finitePrimeSymplecticInclusion v s * Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf) (γ ^ N) *
            (FiniteConjugation.Realization.finitePrimeSymplecticInclusion v s)⁻¹) →
        ∃ ξ : ℂ, ξ ^ 8 = 1 ∧ D.finite.action m Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction = ξ • Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction := by
  obtain ⟨S, hS⟩ := every_rational_tail_power_phase D γ
  refine ⟨insert v S, Finset.mem_insert_self _ _, ?_⟩
  intro T hT N m hm
  have hv : v ∉ (T : Set (HeightOneSpectrum ℤ))ᶜ := by
    exact fun h => h (hT (Finset.mem_insert_self _ _))
  rw [finiteMaskSymplectic_one_prime_conjugation _ v hv] at hm
  exact hS T (Finset.Subset.trans (Finset.subset_insert _ _) hT) N m hm

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FiniteMaskCoordinates.Realization
