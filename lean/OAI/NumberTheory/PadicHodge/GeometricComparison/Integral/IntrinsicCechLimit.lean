import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechLimit

/-! # Intrinsic Cech Limit -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.IntrinsicCechLimit.IntegralIntrinsicCechLimit

noncomputable section

/-! Native integral de Rham H-one identifies with the inverse limit
of the principal quotients of the actual coordinate Cech complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [IsNoetherianRing R] [Module.Flat ℤ R]
  (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] [Smooth X.hom]
  {ι : Type} [Finite ι] (U : ι → X.left.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
  (r : R) (hr : IsRegular r) [IsAdicComplete (Ideal.span {r}) R]

local notation "C" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.complex R X U

def equiv : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X 1 ≃ₗ[R]
    (limit (CochainQuotientLimit.PrincipalCochainQuotient.shiftedDiagram R C r 1) : ModuleCat.{0} R) :=
  (IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.nativeHoneEquiv R X U hU hcover r hr).trans
    (CochainQuotientLimit.PrincipalCochainQuotient.compatibleLimitIso R C r 1).toLinearEquiv

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.IntrinsicCechLimit.IntegralIntrinsicCechLimit
