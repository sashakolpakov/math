import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CommonOpenFiber
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.CommonTransitions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.TransitionDerivation

/-! # Common Open Derivation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CommonOpenDerivation

noncomputable section

/-! Derivation coefficients are constructed from the actual transitions
on a literal affine common open, using its actual scheme special fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] CommonOpenFiber.dualCommonOpenFiber CommonOpenFiber.dualAffineCommonOpenFiber

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k)))) [Smooth X.hom]
    (U : X.left.AffineOpenCover) (V : X.left.affineOpens)

def dualCommonOpenDerivation (i j : U.I₀)
    (hi : V.1 ≤ (U.f i).opensRange) (hj : V.1 ≤ (U.f j).opensRange) :
    Derivation k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X V))
      (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X V)) :=
  AffineProduct.TransitionDerivation.affineProductTransitionDerivation k (CommonOpenFiber.dualAffineCommonOpenFiber k X V)
    (DualOpen.CommonTransitions.dualCommonOpenTransition k X U V.1 i j hi hj)
    (DualOpen.CommonTransitions.dualCommonOpenTransition_reduction k X U V.1 i j hi hj)

theorem dualCommonOpenDerivation_coordinates (i j : U.I₀)
    (hi : V.1 ≤ (U.f i).opensRange) (hj : V.1 ≤ (U.f j).opensRange) :
    (Dual.Derivation.dualDerivationAutomorphism (dualCommonOpenDerivation k X U V i j hi hj)).toAlgHom =
      (CoefficientLiftTensorMap.dualTensorTransitionCoordinates (AffineProduct.Coordinates.affineProductAutomorphismAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X V)
        (DualOpen.CommonTransitions.dualCommonOpenTransition k X U V.1 i j hi hj))).toAlgHom :=
  AffineProduct.TransitionDerivation.affineProductTransitionDerivation_coordinates k (CommonOpenFiber.dualAffineCommonOpenFiber k X V)
    (DualOpen.CommonTransitions.dualCommonOpenTransition k X U V.1 i j hi hj)
    (DualOpen.CommonTransitions.dualCommonOpenTransition_reduction k X U V.1 i j hi hj)

theorem dualCommonOpenTransition_normalForm (i j : U.I₀)
    (hi : V.1 ≤ (U.f i).opensRange) (hj : V.1 ≤ (U.f j).opensRange)
    (u : DualNumber (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X V))) :
    CoefficientLiftTensorMap.dualTensorTransitionCoordinates (AffineProduct.Coordinates.affineProductAutomorphismAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X V)
        (DualOpen.CommonTransitions.dualCommonOpenTransition k X U V.1 i j hi hj)) u =
      (u.fst, dualCommonOpenDerivation k X U V i j hi hj u.fst + u.snd) :=
  AffineProduct.TransitionDerivation.affineProductAutomorphism_normalForm k (CommonOpenFiber.dualAffineCommonOpenFiber k X V)
    (DualOpen.CommonTransitions.dualCommonOpenTransition k X U V.1 i j hi hj)
    (DualOpen.CommonTransitions.dualCommonOpenTransition_reduction k X U V.1 i j hi hj) u

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CommonOpenDerivation
