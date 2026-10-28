import OAI.AlgebraicGeometry.SheafCohomology.Projective.IntegralDimension
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field

/-! # Noether Normalization Dimension -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.NoetherNormalizationDimension.Dimension

noncomputable section

/-! The number of independent parameters in Noether normalization is the actual Krull dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem noetherNormalization_krullDimension
    (K B : Type u) [Field K] [CommRing B] [Nontrivial B]
    [Algebra K B] [Algebra.FiniteType K B] :
    ∃ (g : ℕ) (φ : MvPolynomial (Fin g) K →ₐ[K] B),
      Function.Injective φ ∧ φ.Finite ∧ ringKrullDim B = (g : WithBot ℕ∞) := by
  obtain ⟨g, φ, hφ, hfin⟩ := exists_finite_inj_algHom_of_fg K B
  let f : Spec (.of B) ⟶ Spec (.of (MvPolynomial (Fin g) K)) :=
    Spec.map (CommRingCat.ofHom φ.toRingHom)
  have : IsFinite f := (IsFinite.SpecMap_iff _).mpr hfin
  have hi : φ.toRingHom.IsIntegral :=
    (IsIntegralHom.SpecMap_iff (φ := CommRingCat.ofHom φ.toRingHom)).mp
      (inferInstance : IsIntegralHom f)
  have : Surjective f := ⟨hi.comap_surjective hφ⟩
  have he := IntegralDimension.Dimension.topologicalKrullDim_eq_of_integral_surjective f
  change topologicalKrullDim (PrimeSpectrum B) =
    topologicalKrullDim (PrimeSpectrum (MvPolynomial (Fin g) K)) at he
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    zero_add] at he
  refine ⟨g, φ, hφ, hfin, ?_⟩
  simpa only [ENat.card_eq_coe_fintype_card, Fintype.card_fin, WithBot.coe_natCast] using he

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.NoetherNormalizationDimension.Dimension
