import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.LineTangentBoundary
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.BoundaryShuffle
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Fixed.CechCover
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.RegularSections

/-! # Line Intrinsic Class -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.LineIntrinsicClass

noncomputable section

/-! The actual tangent cocycle contracted with an original family
line bundle's logarithmic transitions is a boundary in the native
fixed-fiber structure-sheaf Cech complex. Its native H2 class is zero. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k] (X : Over (Spec (.of R))) [Smooth X.hom] [IsSeparated X.hom]
    (U : X.left.AffineOpenCover)
    (D : HilbertConstruction.OpenFrame.Transitions.OpenFrameTransitions (fun i => (AffineCoverIntersections.familyCoverAffineOpen R X U i).1))

attribute [local implicit_reducible] AffineCoverIntersections.familyCoverPairAffineOpen AffineCoverIntersections.familyCoverTripleAffineOpen
attribute [local implicit_reducible] Fixed.CechCover.fixedFamilyCechCover TangentBasePoint.fixedFamilyFiber FixedFiber.CoordinateProjection.fixedFiberAffineOpen
attribute [local irreducible] FixedFiber.RegularSections.fixedFiberRegularSectionEquiv

local instance familyLineNativeH2AddCommGroup :
    AddCommGroup (CategoryTheory.Sheaf.H (Dual.UnitCechClasses.ringAdditiveSheaf (TangentBasePoint.fixedFamilyFiber k R X).left.sheaf) 2) :=
  Regular.BoundaryShuffle.regularTripleH2AddCommGroup (TangentBasePoint.fixedFamilyFiber k R X).left

def familyLineLogRegularPair (d : Derivation k R k) (i j : U.I₀) :
    Γ((TangentBasePoint.fixedFamilyFiber k R X).left, Fixed.CechCover.fixedFamilyCechCover k R X U i ⊓ Fixed.CechCover.fixedFamilyCechCover k R X U j) :=
  FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R k X (AffineCoverIntersections.familyCoverPairAffineOpen R X U i j)
    (LineTangentBoundary.familyLineLogPair k R X U D i j d)

def familyLineTangentRegularTriple (d : Derivation k R k) (i j l : U.I₀) :
    Γ((TangentBasePoint.fixedFamilyFiber k R X).left,
      (Fixed.CechCover.fixedFamilyCechCover k R X U i ⊓ Fixed.CechCover.fixedFamilyCechCover k R X U j) ⊓ Fixed.CechCover.fixedFamilyCechCover k R X U l) :=
  FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R k X (AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l)
    (LineTangentBoundary.familyLineTangentTriple k R X U D d i j l)

theorem familyLineTangentRegularTriple_boundary (d : Derivation k R k) :
    Regular.BoundaryShuffle.RegularTripleBoundary (TangentBasePoint.fixedFamilyFiber k R X).left (Fixed.CechCover.fixedFamilyCechCover k R X U)
      (familyLineLogRegularPair k R X U D d) (familyLineTangentRegularTriple k R X U D d) := by
  intro i j l
  have h := congrArg (FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R k X (AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l))
    (LineTangentBoundary.familyLineTangentTriple_boundary k R X U D d i j l)
  rw [map_add, map_sub, FixedFiber.RegularSections.fixedFiberRegularSectionEquiv_restrict,
    FixedFiber.RegularSections.fixedFiberRegularSectionEquiv_restrict, FixedFiber.RegularSections.fixedFiberRegularSectionEquiv_restrict] at h
  exact h

def familyLineTangentSheafClass (d : Derivation k R k) :
    CategoryTheory.Sheaf.H (Dual.UnitCechClasses.ringAdditiveSheaf (TangentBasePoint.fixedFamilyFiber k R X).left.sheaf) 2 :=
  DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (Fixed.CechCover.fixedFamilyCechCover k R X U) (Dual.UnitCechClasses.ringAdditiveSheaf (TangentBasePoint.fixedFamilyFiber k R X).left.sheaf)
    (Fixed.CechCover.fixedFamilyCechCover_covers k R X U) 1
    (Regular.BoundaryShuffle.regularTripleCechCochain (TangentBasePoint.fixedFamilyFiber k R X).left (Fixed.CechCover.fixedFamilyCechCover k R X U)
      (familyLineTangentRegularTriple k R X U D d))
    (Regular.BoundaryShuffle.regularTripleCechCochain_closed (TangentBasePoint.fixedFamilyFiber k R X).left (Fixed.CechCover.fixedFamilyCechCover k R X U)
      (familyLineLogRegularPair k R X U D d) (familyLineTangentRegularTriple k R X U D d)
      (familyLineTangentRegularTriple_boundary k R X U D d))

theorem familyLineTangentSheafClass_eq_zero (d : Derivation k R k) :
    familyLineTangentSheafClass k R X U D d = 0 :=
  Regular.BoundaryShuffle.regularTripleCechClass_eq_zero (TangentBasePoint.fixedFamilyFiber k R X).left (Fixed.CechCover.fixedFamilyCechCover k R X U)
    (Fixed.CechCover.fixedFamilyCechCover_covers k R X U) (familyLineLogRegularPair k R X U D d)
    (familyLineTangentRegularTriple k R X U D d) (familyLineTangentRegularTriple_boundary k R X U D d)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.LineIntrinsicClass
