import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.DualMap

/-! # Dual Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.DualCoordinates

noncomputable section

/-! The inverse used by common-resolution duality has its literal
homology-map coordinate before specialization to the canonical twist. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (M N : (Proj (homogeneousSubmodule σ R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent] [N.IsFiniteType]
  (j : σ) (B b : ℕ) (hb : b ≤ B) (f : M ⟶ N) (q : ℕ)

omit [LinearOrder σ] in
theorem leftIso_hom : (DualMap.leftIso M N j B b hb f q).hom =
    HomologicalComplex.homologyMap (DualMap.leftMap M N j B b f) q := rfl

omit [LinearOrder σ] in
theorem map_left : DualMap.map M N j B b hb f q ≫
    HomologicalComplex.homologyMap (DualMap.leftMap M N j B b f) q =
      HomologicalComplex.homologyMap (DualMap.rightMap M N j B b f) q := by
  rw [← leftIso_hom M N j B b hb f q]
  exact DualMap.map_left M N j B b hb f q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.DualCoordinates
