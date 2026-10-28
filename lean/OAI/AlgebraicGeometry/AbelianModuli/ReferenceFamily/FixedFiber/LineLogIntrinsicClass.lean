import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.LineLogCocycle
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Fixed.CechCover
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.RegularSections
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.Closed

/-! # Line Log Intrinsic Class -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.LineLogIntrinsicClass

noncomputable section

/-! The original line-frame logarithmic cocycle in each constant
conormal direction defines a class in the original fixed-fiber H1. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable (R : Type) [CommRing R] [Algebra R ℂ] (X : Over (Spec (.of R))) [IsSeparated X.hom]
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R X)] (U : X.left.AffineOpenCover)
    (D : HilbertConstruction.OpenFrame.Transitions.OpenFrameTransitions (fun i => (Family.AffineCoverIntersections.familyCoverAffineOpen R X U i).1))
    (l : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X) →ₗ[ℂ] ℂ)

attribute [local implicit_reducible] Family.AffineCoverIntersections.familyCoverAffineOpen Family.AffineCoverIntersections.familyCoverPairAffineOpen Family.AffineCoverIntersections.familyCoverTripleAffineOpen
attribute [local implicit_reducible] Fixed.CechCover.fixedFamilyCechCover TangentBasePoint.fixedFamilyFiber CoordinateProjection.fixedFiberAffineOpen
attribute [local irreducible] RegularSections.fixedFiberRegularSectionEquiv

def fixedFiberLineLogPair (i j : U.I₀) :
    ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j) :=
  LineLogCocycle.fixedFiberLineLogCoefficient R X _ D l (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j) i j inf_le_left inf_le_right

def fixedFiberLineLogRegularPair (i j : U.I₀) :
    Γ((TangentBasePoint.fixedFamilyFiber ℂ R X).left, Fixed.CechCover.fixedFamilyCechCover ℂ R X U i ⊓ Fixed.CechCover.fixedFamilyCechCover ℂ R X U j) :=
  RegularSections.fixedFiberRegularSectionEquiv R ℂ X (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j)
    (fixedFiberLineLogPair R X U D l i j)

theorem fixedFiberLineLogPair_cocycle (i j m : U.I₀) :
    DerivationPresheaf.fixedFiberTensorRestriction R ℂ X
        (show (Family.AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j m).1 ≤ (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 from inf_le_left)
        (fixedFiberLineLogPair R X U D l i j) +
      DerivationPresheaf.fixedFiberTensorRestriction R ℂ X
        (show (Family.AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j m).1 ≤ (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U j m).1 from
          le_inf (inf_le_left.trans inf_le_right) inf_le_right) (fixedFiberLineLogPair R X U D l j m) =
      DerivationPresheaf.fixedFiberTensorRestriction R ℂ X
        (show (Family.AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j m).1 ≤ (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i m).1 from
          le_inf (inf_le_left.trans inf_le_left) inf_le_right) (fixedFiberLineLogPair R X U D l i m) := by
  unfold fixedFiberLineLogPair
  rw [← LineLogCocycle.fixedFiberLineLogCoefficient_restrict, ← LineLogCocycle.fixedFiberLineLogCoefficient_restrict,
    ← LineLogCocycle.fixedFiberLineLogCoefficient_restrict]
  exact LineLogCocycle.fixedFiberLineLogCoefficient_cocycle R X _ D l (Family.AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j m)
    i j m (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right

theorem fixedFiberLineLogRegularPair_cocycle :
    RegularPair.Closed.RegularPairCocycle (TangentBasePoint.fixedFamilyFiber ℂ R X).left (Fixed.CechCover.fixedFamilyCechCover ℂ R X U)
      (fixedFiberLineLogRegularPair R X U D l) := by
  intro i j m
  have h := congrArg (RegularSections.fixedFiberRegularSectionEquiv R ℂ X (Family.AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j m))
    (fixedFiberLineLogPair_cocycle R X U D l i j m)
  rw [map_add, RegularSections.fixedFiberRegularSectionEquiv_restrict, RegularSections.fixedFiberRegularSectionEquiv_restrict,
    RegularSections.fixedFiberRegularSectionEquiv_restrict] at h
  exact h

def fixedFiberLineLogSheafClass :
    SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule (TangentBasePoint.fixedFamilyFiber ℂ R X).left) 1 :=
  RegularPair.Closed.regularPairSheafClass (TangentBasePoint.fixedFamilyFiber ℂ R X).left (Fixed.CechCover.fixedFamilyCechCover ℂ R X U)
    (Fixed.CechCover.fixedFamilyCechCover_covers ℂ R X U) (fixedFiberLineLogRegularPair R X U D l)
    (fixedFiberLineLogRegularPair_cocycle R X U D l)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.LineLogIntrinsicClass
