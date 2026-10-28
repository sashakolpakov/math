import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Quadratic

/-! # Quadratic Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QuadraticProjection.CM

noncomputable section

/-! Quadratic phases commute with actual rational-algebra projections. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
variable {I K L : Type*} [Fintype I] [CommRing K] [CommRing L] [Algebra ℚ K] [Algebra ℚ L]

theorem quadratic_map (f : K →ₐ[ℚ] L) (B : Matrix I I K) (x : I → K) :
    f (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B x) = RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic (B.map f) (fun i => f (x i)) := by
  simp only [RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic_entries, map_sum, map_mul, AlgHom.commutes, Matrix.map_apply]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QuadraticProjection.CM
