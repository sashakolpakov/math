import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Etale.Basic

/-! # Differential Etale Criterion -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.DifferentialEtaleCriterion.BundleCycles

noncomputable section

/-! # LineBundleCycles: an actual differential isomorphism supplies the local étale criterion -/

open KaehlerDifferential TensorProduct

variable (R S T : Type) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.FormallySmooth R T]

theorem formallyEtale_of_differential_bijective
    (h : Function.Bijective (mapBaseChange R S T)) : Algebra.FormallyEtale S T := by
  have hΩ : ∀ x : Ω[T⁄S], x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := map_surjective R S T x
    obtain ⟨z, rfl⟩ := h.surjective y
    exact (exact_mapBaseChange_map R S T (mapBaseChange R S T z)).mpr ⟨z, rfl⟩
  have hH : ∀ x : Algebra.H1Cotangent S T, x = 0 := by
    intro x
    have hz : Algebra.H1Cotangent.δ R S T x = 0 := by
      apply h.injective
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T _).mpr ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := (Algebra.H1Cotangent.exact_map_δ R S T x).mp hz
    exact hy.symm.trans ((congrArg (Algebra.H1Cotangent.map R S T T)
      (Subsingleton.elim y 0)).trans (map_zero _))
  exact ⟨⟨fun x y => (hΩ x).trans (hΩ y).symm⟩, ⟨fun x y => (hH x).trans (hH y).symm⟩⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.DifferentialEtaleCriterion.BundleCycles
