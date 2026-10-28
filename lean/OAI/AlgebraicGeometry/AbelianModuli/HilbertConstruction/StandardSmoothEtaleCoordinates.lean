import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferentialCoordinatesEtale
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-! # Standard Smooth Etale Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StandardSmoothEtaleCoordinates

noncomputable section

/-! A standard smooth algebra of dimension g admits an actual etale polynomial-coordinate map with g parameters, constructed from the complementary variables of its submersive presentation. -/
open _root_.Algebra
universe u v

theorem exists_etale_polynomial_coordinates_of_standardSmooth
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (g : ℕ) [IsStandardSmoothOfRelativeDimension g R S] :
    ∃ (ι : Type) (_ : Finite ι) (x : ι → S),
      Nat.card ι = g ∧ (MvPolynomial.aeval x : MvPolynomial ι R →ₐ[R] S).toRingHom.Etale := by
  classical
  obtain ⟨ι, σ, hσ, hι, P, hP⟩ :=
    (inferInstance : IsStandardSmoothOfRelativeDimension g R S).out
  let : Finite σ := hσ
  let : Finite ι := hι
  let : Fintype σ := Fintype.ofFinite σ
  let : Fintype ι := Fintype.ofFinite ι
  let κ := ((Set.range P.map)ᶜ : Set ι)
  let x : κ → S := fun i => P.val i.val
  have hcard : Nat.card κ = P.dimension := by
    simp only [κ, Presentation.dimension, Nat.card_eq_fintype_card,
      Fintype.card_compl_set, Set.card_range_of_injective P.map_inj]
  have : IsStandardSmooth R S := P.isStandardSmooth
  refine ⟨κ, inferInstance, x, hcard.trans hP, ?_⟩
  exact DifferentialCoordinatesEtale.etale_aeval_of_basis_differentials R S x P.basisKaehler
    (fun i => P.basisKaehler_apply i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StandardSmoothEtaleCoordinates
