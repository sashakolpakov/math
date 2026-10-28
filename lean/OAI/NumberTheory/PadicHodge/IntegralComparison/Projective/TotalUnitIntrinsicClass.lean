import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TotalUnitCoordinates

/-! # Total Unit Intrinsic Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TotalUnitIntrinsicClass.Intrinsic

noncomputable section

/-! The native right/inverse-left map on the fixed point's trace unit
is the original total unit class itself. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.UnitTrace
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (M N : (Proj (homogeneousSubmodule σ R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent] [N.IsFiniteType]
  (B n : ℕ) (hn : Fintype.card σ = n+2) (hB : n+2 ≤ B) (f : M ⟶ N)
  (eM : TopTracePairing.coefficientRing R ≃ₗ[TopTracePairing.coefficientRing R] ProjectiveTower.UnitTrace.cohomology M 0)
  (eN : TopTracePairing.coefficientRing R ≃ₗ[TopTracePairing.coefficientRing R] ProjectiveTower.UnitTrace.cohomology N 0)

theorem unitClass : TotalUnitCoordinates.nativeMap M N B n hn hB f
    ((TotalUnitMap.fixedTrace N B n hn hB eN).inv 1) =
    TotalUnitMap.unitClass M N B n hn hB f eM eN := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TotalUnitIntrinsicClass.Intrinsic
