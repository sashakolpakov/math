import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.ConstantDerivations
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.FrameCoordinateUnits

/-! # Line Log Cocycle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.LineLogCocycle

noncomputable section

/-! Original line-frame units reduce in the actual fixed-fiber
tensor coordinates. Applying a constant native conormal direction to
their logarithms gives a restricted additive cocycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (R k : Type) [CommRing R] [CommRing k] [Algebra R k]
    (X : Over (Spec (.of R))) {I : Type} (U : I → X.left.Opens) (D : HilbertConstruction.OpenFrame.Transitions.OpenFrameTransitions U)

def fixedFiberFrameReducedUnit (V : X.left.affineOpens) (i j : I) (hi : V.1 ≤ U i) (hj : V.1 ≤ U j) :
    (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)ˣ :=
  Units.map (algebraMap (Family.AffineTangentLifts.familyAffineRing R X V) (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)).toMonoidHom
    (Family.FrameCoordinateUnits.familyFrameCoordinateUnit R X U D V i j hi hj)

theorem fixedFiberFrameReducedUnit_restrict {V W : X.left.affineOpens} (h : V.1 ≤ W.1)
    (i j : I) (hi : W.1 ≤ U i) (hj : W.1 ≤ U j) :
    Units.map (DerivationPresheaf.fixedFiberTensorRestriction R k X h).toMonoidHom (fixedFiberFrameReducedUnit R k X U D W i j hi hj) =
      fixedFiberFrameReducedUnit R k X U D V i j (h.trans hi) (h.trans hj) := by
  apply Units.ext
  have he := congrArg Units.val (Family.FrameCoordinateUnits.familyFrameCoordinateUnit_restrict R X U D h i j hi hj)
  exact congrArg (fun a : Family.AffineTangentLifts.familyAffineRing R X V => (1 : k) ⊗ₜ[R] a) he

theorem fixedFiberFrameReducedUnit_cocycle (V : X.left.affineOpens) (i j l : I)
    (hi : V.1 ≤ U i) (hj : V.1 ≤ U j) (hl : V.1 ≤ U l) :
    fixedFiberFrameReducedUnit R k X U D V i j hi hj * fixedFiberFrameReducedUnit R k X U D V j l hj hl =
      fixedFiberFrameReducedUnit R k X U D V i l hi hl := by
  unfold fixedFiberFrameReducedUnit
  rw [← map_mul, Family.FrameCoordinateUnits.familyFrameCoordinateUnit_cocycle]

omit k [CommRing k] [Algebra R k]

variable [Algebra R ℂ] [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R X).left]
    [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R X).hom] [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R X)]
    (l : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X) →ₗ[ℂ] ℂ)

def fixedFiberLineLogCoefficient (V : X.left.affineOpens) (i j : I)
    (hi : V.1 ≤ U i) (hj : V.1 ≤ U j) : ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V :=
  CoefficientUnitLogarithms.coefficientUnitLog (ConstantDerivations.fixedFiberConstantConormalDerivation R X V l)
    (fixedFiberFrameReducedUnit R ℂ X U D V i j hi hj)

theorem fixedFiberLineLogCoefficient_restrict {V W : X.left.affineOpens} (h : V.1 ≤ W.1)
    (i j : I) (hi : W.1 ≤ U i) (hj : W.1 ≤ U j) :
    fixedFiberLineLogCoefficient R X U D l V i j (h.trans hi) (h.trans hj) =
      DerivationPresheaf.fixedFiberTensorRestriction R ℂ X h (fixedFiberLineLogCoefficient R X U D l W i j hi hj) := by
  unfold fixedFiberLineLogCoefficient
  rw [← fixedFiberFrameReducedUnit_restrict R ℂ X U D h i j hi hj]
  exact ConstantDerivations.fixedFiberConstantConormalUnitLog_restrict R X h l _

theorem fixedFiberLineLogCoefficient_cocycle (V : X.left.affineOpens) (i j m : I)
    (hi : V.1 ≤ U i) (hj : V.1 ≤ U j) (hm : V.1 ≤ U m) :
    fixedFiberLineLogCoefficient R X U D l V i j hi hj + fixedFiberLineLogCoefficient R X U D l V j m hj hm =
      fixedFiberLineLogCoefficient R X U D l V i m hi hm := by
  unfold fixedFiberLineLogCoefficient
  rw [← CoefficientUnitLogarithms.coefficientUnitLog_mul, fixedFiberFrameReducedUnit_cocycle]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.LineLogCocycle
