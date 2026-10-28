import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.Serre
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.DualCoordinates

/-! # Fixed Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.FixedMap

noncomputable section

/-! The common-resolution map expressed in the original fixed-dual
complexes used by the projective Serre pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (M N : (Proj (homogeneousSubmodule σ R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent] [N.IsFiniteType]
  (B n : ℕ) (hn : Fintype.card σ = n + 2) (hB : n + 2 ≤ B) (f : M ⟶ N) (c : ℕ)

def map : (Serre.fixedDual N B n hn).homology c ⟶
    (Serre.fixedDual M B n hn).homology c :=
  DualMap.map M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B (n + 2) hB f c

omit [Module.Injective R R] in
theorem map_left : FixedMap.map M N B n hn hB f c ≫ HomologicalComplex.homologyMap
    ((Affine.LocalDualInvariance.functor (Projective.TopTracePairing.canonicalTwist (R := R) n hn)).map
      (Projective.NegativeRefinement.leftHom M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B f).chainMap.op) c =
    HomologicalComplex.homologyMap
      ((Affine.LocalDualInvariance.functor (Projective.TopTracePairing.canonicalTwist (R := R) n hn)).map
        (Projective.NegativeRefinement.rightHom M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B f).chainMap.op) c :=
  DualCoordinates.map_left M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B (n + 2) hB f c

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.FixedMap
