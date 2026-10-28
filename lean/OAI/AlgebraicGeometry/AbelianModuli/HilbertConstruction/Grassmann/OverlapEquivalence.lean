import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.OverlapFunctor

/-! # Overlap Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.OverlapEquivalence

noncomputable section

/-! Natural equivalence between the two coordinate descriptions of a Grassmannian chart overlap. -/

open _root_.CategoryTheory

universe u

variable {A : Type u} [CommRing A] {k l : ℕ}

/-- A point on an overlap gives a valid point in the reverse overlap after changing frames. -/
theorem grassmannPermute_reverse_valid (c : Charts.GrassmannChart A (Fin l → A) k)
    (τ : Equiv.Perm (Fin k ⊕ Fin l))
    (h : Function.Bijective ((Charts.grassmannQuotientChartEquiv c).firstBlock
      (Chart.CoordinatePermutations.chartCoordinatePermutation A τ).toLinearMap)) :
    Function.Bijective ((Charts.grassmannQuotientChartEquiv (Charts.GrassmannChart.permute c τ h)).firstBlock
      (Chart.CoordinatePermutations.chartCoordinatePermutation A τ.symm).toLinearMap) := by
  rw [← Chart.PermutationCoherence.chartCoordinatePermutation_symm]
  exact (Charts.grassmannQuotientChartEquiv c).transition_inverse_bijective (Chart.CoordinatePermutations.chartCoordinatePermutation A τ) h

/-- Reversing the change of frame recovers the initial quotient-chart point. -/
theorem grassmannPermute_reverse (c : Charts.GrassmannChart A (Fin l → A) k)
    (τ : Equiv.Perm (Fin k ⊕ Fin l))
    (h : Function.Bijective ((Charts.grassmannQuotientChartEquiv c).firstBlock
      (Chart.CoordinatePermutations.chartCoordinatePermutation A τ).toLinearMap)) :
    Charts.GrassmannChart.permute (Charts.GrassmannChart.permute c τ h) τ.symm
      (grassmannPermute_reverse_valid c τ h) = c := by
  apply Charts.grassmannQuotientChartEquiv.injective
  change ((Charts.grassmannQuotientChartEquiv c).transition (Chart.CoordinatePermutations.chartCoordinatePermutation A τ).toLinearMap h).transition
    (Chart.CoordinatePermutations.chartCoordinatePermutation A τ.symm).toLinearMap _ = Charts.grassmannQuotientChartEquiv c
  simpa only [Chart.PermutationCoherence.chartCoordinatePermutation_symm] using
    (Charts.grassmannQuotientChartEquiv c).transition_inverse (Chart.CoordinatePermutations.chartCoordinatePermutation A τ) h

/-- Pointwise equivalence of the two descriptions of an overlap. -/
def grassmannOverlapPointEquiv (τ : Equiv.Perm (Fin k ⊕ Fin l)) :
    LocalizationChartParameters.GrassmannOverlapPoint τ A ≃ LocalizationChartParameters.GrassmannOverlapPoint τ.symm A where
  toFun c := ⟨Charts.GrassmannChart.permute c.val τ c.property, grassmannPermute_reverse_valid c.val τ c.property⟩
  invFun c := ⟨Charts.GrassmannChart.permute c.val τ.symm c.property,
    grassmannPermute_reverse_valid c.val τ.symm c.property⟩
  left_inv c := Subtype.ext (grassmannPermute_reverse c.val τ c.property)
  right_inv c := Subtype.ext (grassmannPermute_reverse c.val τ.symm c.property)

/-- The overlap equivalence is natural in the coefficient algebra. -/
def grassmannOverlapFunctorIso (R : Type u) [CommRing R] (τ : Equiv.Perm (Fin k ⊕ Fin l)) :
    OverlapFunctor.grassmannOverlapFunctor R τ ≅ OverlapFunctor.grassmannOverlapFunctor R τ.symm :=
  NatIso.ofComponents (fun A => (grassmannOverlapPointEquiv (A := A) τ).toIso) (by
    intro A B f
    apply ConcreteCategory.hom_ext
    intro c
    exact Subtype.ext (Charts.GrassmannChart.permute_naturality f.hom.toRingHom c.val τ c.property).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.OverlapEquivalence
