import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.FiniteType

/-! # Type Ring Dimension Bound -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Finite.TypeRingDimensionBound.Construction

noncomputable section

/-! Finite dimension bounds for arbitrary finite-type algebras over a field. -/

theorem finiteType_ringKrullDim_bounded
    (k R : Type*) [Field k] [CommRing R] [Algebra k R] [Algebra.FiniteType k R] :
    ∃ d : ℕ, ringKrullDim R ≤ d := by
  obtain ⟨n, φ, hφ⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := k) (S := R)).mp inferInstance
  refine ⟨n, ?_⟩
  have h := ringKrullDim_le_of_surjective φ.toRingHom hφ
  simpa [MvPolynomial.ringKrullDim_of_isNoetherianRing] using h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Finite.TypeRingDimensionBound.Construction
