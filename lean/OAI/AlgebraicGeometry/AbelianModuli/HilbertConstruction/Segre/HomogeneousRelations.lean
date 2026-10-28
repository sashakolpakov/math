import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.NormalizedQuotient
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-! # Homogeneous Relations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.HomogeneousRelations

noncomputable section

/-! The Segre equations form a homogeneous ideal whose normalized chart is already explicit. -/

open _root_.MvPolynomial

universe u v w

variable (R : Type u) [CommRing R] {σ : Type v} {τ : Type w}

local instance : GradedAlgebra (MvPolynomial.homogeneousSubmodule (σ × τ) R) :=
  MvPolynomial.gradedAlgebra

theorem segreMinor_homogeneous (a c : σ) (b d : τ) :
    IsHomogeneous (NormalizedCoordinates.segreMinor R a c b d) 2 :=
  ((isHomogeneous_X R (a, b)).mul (isHomogeneous_X R (c, d))).sub
    ((isHomogeneous_X R (a, d)).mul (isHomogeneous_X R (c, b)))

def segreHomogeneousIdeal : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (σ × τ) R) where
  toSubmodule := Ideal.span
    (Set.range (fun q : (σ × τ) × (σ × τ) => NormalizedCoordinates.segreMinor R q.1.1 q.2.1 q.1.2 q.2.2))
  is_homogeneous' := Ideal.homogeneous_span _ _ (by
    rintro _ ⟨q, rfl⟩
    exact ⟨2, segreMinor_homogeneous R q.1.1 q.2.1 q.1.2 q.2.2⟩)

theorem segreNormalizedIdeal_eq_sup (i : σ) (j : τ) :
    NormalizedCoordinates.segreNormalizedIdeal R i j = (segreHomogeneousIdeal (σ := σ) (τ := τ) R).toIdeal ⊔
      Ideal.span {X (i, j) - 1} := by
  rw [NormalizedCoordinates.segreNormalizedIdeal, Ideal.span_insert, sup_comm]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.HomogeneousRelations
