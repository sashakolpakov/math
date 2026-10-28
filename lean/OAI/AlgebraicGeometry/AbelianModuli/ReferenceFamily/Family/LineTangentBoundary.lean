import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.UnitLogarithms
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.FrameCoordinateUnits
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections

/-! # Line Tangent Boundary -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.LineTangentBoundary

noncomputable section

/-! A line bundle on the original smooth family supplies an explicit
primitive for the contraction of the tangent-chart cocycle with its
logarithmic transition cocycle. No trivialization of the whole family
or lifting of an arbitrarily chosen special-fiber bundle is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k] (X : Over (Spec (.of R))) [Smooth X.hom] [IsSeparated X.hom]
    (U : X.left.AffineOpenCover)
    (D : HilbertConstruction.OpenFrame.Transitions.OpenFrameTransitions (fun i => (AffineCoverIntersections.familyCoverAffineOpen R X U i).1))

attribute [local instance 50] AffineTangentLifts.familyAffineCoefficientAlgebra
attribute [local instance] AffineTangentLifts.familyAffineCoefficientTower Algebra.TensorProduct.rightAlgebra
attribute [local instance] PointFiberTensorLifts.pointFiberTensor_scalarTower
attribute [local implicit_reducible] AffineCoverIntersections.familyCoverAffineOpen AffineCoverIntersections.familyCoverPairAffineOpen AffineCoverIntersections.familyCoverTripleAffineOpen

def familyLineLogPair (i j : U.I₀) :
    Derivation k R k →ₗ[k] (k ⊗[R] AffineTangentLifts.familyAffineRing R X (AffineCoverIntersections.familyCoverPairAffineOpen R X U i j)) :=
  UnitLogarithms.familyRestrictedUnitLog k R X
    (show (AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 ≤ (AffineCoverIntersections.familyCoverAffineOpen R X U i).1 from inf_le_left)
    (FrameCoordinateUnits.familyFrameCoordinateUnit R X _ D (AffineCoverIntersections.familyCoverPairAffineOpen R X U i j) i j inf_le_left inf_le_right)

def familyLineTangentTriple (d : Derivation k R k) (i j l : U.I₀) :
    k ⊗[R] AffineTangentLifts.familyAffineRing R X (AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l) :=
  let V := AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l
  let hi : V.1 ≤ (AffineCoverIntersections.familyCoverAffineOpen R X U i).1 := inf_le_left.trans inf_le_left
  let hj : V.1 ≤ (AffineCoverIntersections.familyCoverAffineOpen R X U j).1 := inf_le_left.trans inf_le_right
  let hl : V.1 ≤ (AffineCoverIntersections.familyCoverAffineOpen R X U l).1 := inf_le_right
  let u := FrameCoordinateUnits.familyFrameCoordinateUnit R X _ D V j l hj hl
  CommonOpenTangentDifferences.familyCommonOpenTangentDifference k R X hi hj d ((1 : k) ⊗ₜ[R] u.val) *
    ((1 : k) ⊗ₜ[R] (u⁻¹).val)

theorem familyLineTangentTriple_boundary (d : Derivation k R k) (i j l : U.I₀) :
    FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R k X
        (show (AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l).1 ≤ (AffineCoverIntersections.familyCoverPairAffineOpen R X U j l).1 from
          le_inf (inf_le_left.trans inf_le_right) inf_le_right) (familyLineLogPair k R X U D j l d) -
      FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R k X
        (show (AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l).1 ≤ (AffineCoverIntersections.familyCoverPairAffineOpen R X U i l).1 from
          le_inf (inf_le_left.trans inf_le_left) inf_le_right) (familyLineLogPair k R X U D i l d) +
      FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R k X
        (show (AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l).1 ≤ (AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 from
          inf_le_left) (familyLineLogPair k R X U D i j d) =
      familyLineTangentTriple k R X U D d i j l := by
  unfold familyLineLogPair
  rw [← UnitLogarithms.familyRestrictedUnitLog_restrict, ← UnitLogarithms.familyRestrictedUnitLog_restrict,
    ← UnitLogarithms.familyRestrictedUnitLog_restrict]
  rw [FrameCoordinateUnits.familyFrameCoordinateUnit_restrict, FrameCoordinateUnits.familyFrameCoordinateUnit_restrict,
    FrameCoordinateUnits.familyFrameCoordinateUnit_restrict]
  exact UnitLogarithms.familyRestrictedUnitLog_triangle k R X
    (show (AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l).1 ≤ (AffineCoverIntersections.familyCoverAffineOpen R X U i).1 from
      inf_le_left.trans inf_le_left)
    (show (AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l).1 ≤ (AffineCoverIntersections.familyCoverAffineOpen R X U j).1 from
      inf_le_left.trans inf_le_right) _ _ _
    (FrameCoordinateUnits.familyFrameCoordinateUnit_cocycle R X _ D (AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l)
      i j l (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right).symm d

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.LineTangentBoundary
