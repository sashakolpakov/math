import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.LineTangentConormalExpansion
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.CupSymmetry

/-! # Line Tangent Cup Boundary -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.LineTangentCupBoundary

noncomputable section

/-! The original tangent and line-logarithm H1 cocycles satisfy an
actual native H2 cup constraint, with an explicit primitive on the
original fixed-fiber cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.CategoryTheory.MonObj BigOperators

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (X : Over (Spec (.of R))) [Smooth X.hom] [IsSeparated X.hom]
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R X)] (U : X.left.AffineOpenCover)
    (D : HilbertConstruction.OpenFrame.Transitions.OpenFrameTransitions (fun i => (AffineCoverIntersections.familyCoverAffineOpen R X U i).1))
    {I : Type} [Fintype I] (b : Module.Basis I ℂ (Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X)))

def familyLineTangentCupTriple (d : Derivation ℂ R ℂ) (i j l : U.I₀) :
    Γ((TangentBasePoint.fixedFamilyFiber ℂ R X).left,
      (Fixed.CechCover.fixedFamilyCechCover ℂ R X U i ⊓ Fixed.CechCover.fixedFamilyCechCover ℂ R X U j) ⊓ Fixed.CechCover.fixedFamilyCechCover ℂ R X U l) :=
  ∑ a, RegularPair.CupSymmetry.regularPairCupTriple (TangentBasePoint.fixedFamilyFiber ℂ R X).left (Fixed.CechCover.fixedFamilyCechCover ℂ R X U)
    (FamilyTangent.RegularCocycle.familyTangentRegularPair R X U d (b a)) (FixedFiber.LineLogIntrinsicClass.fixedFiberLineLogRegularPair R X U D (b.coord a)) i j l

theorem familyLineTangentCupTriple_boundary (d : Derivation ℂ R ℂ) :
    Regular.BoundaryShuffle.RegularTripleBoundary (TangentBasePoint.fixedFamilyFiber ℂ R X).left (Fixed.CechCover.fixedFamilyCechCover ℂ R X U)
      (LineIntrinsicClass.familyLineLogRegularPair ℂ R X U D d) (familyLineTangentCupTriple R X U D b d) := by
  intro i j l
  exact (LineIntrinsicClass.familyLineTangentRegularTriple_boundary ℂ R X U D d i j l).trans
    (LineTangentConormalExpansion.familyLineTangentRegularTriple_conormalExpansion R X U D b d i j l)

theorem familyLineTangentCupClass_eq_zero (d : Derivation ℂ R ℂ) :
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (Fixed.CechCover.fixedFamilyCechCover ℂ R X U)
      (Dual.UnitCechClasses.ringAdditiveSheaf (TangentBasePoint.fixedFamilyFiber ℂ R X).left.sheaf) (Fixed.CechCover.fixedFamilyCechCover_covers ℂ R X U) 1
      (Regular.BoundaryShuffle.regularTripleCechCochain (TangentBasePoint.fixedFamilyFiber ℂ R X).left (Fixed.CechCover.fixedFamilyCechCover ℂ R X U)
        (familyLineTangentCupTriple R X U D b d))
      (Regular.BoundaryShuffle.regularTripleCechCochain_closed (TangentBasePoint.fixedFamilyFiber ℂ R X).left (Fixed.CechCover.fixedFamilyCechCover ℂ R X U)
        (LineIntrinsicClass.familyLineLogRegularPair ℂ R X U D d) (familyLineTangentCupTriple R X U D b d)
        (familyLineTangentCupTriple_boundary R X U D b d)) =
      (0 : (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology (TangentBasePoint.fixedFamilyFiber ℂ R X).left.toPresheafedSpace.carrier) 2).obj
          (Dual.UnitCechClasses.ringAdditiveSheaf (TangentBasePoint.fixedFamilyFiber ℂ R X).left.sheaf)) :=
  Regular.BoundaryShuffle.regularTripleCechClass_eq_zero (TangentBasePoint.fixedFamilyFiber ℂ R X).left (Fixed.CechCover.fixedFamilyCechCover ℂ R X U)
    (Fixed.CechCover.fixedFamilyCechCover_covers ℂ R X U) _ _ (familyLineTangentCupTriple_boundary R X U D b d)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.LineTangentCupBoundary
