import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.LineTangentCupBoundary
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.LineFrameCover
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.TangentIntegralAction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.GraphBundles

/-! # Graph Intrinsic Cup Constraint -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.GraphIntrinsicCupConstraint

noncomputable section

/-! Every original polarized abelian family satisfies the native
cup constraint for its canonical graph bundle. All affine frames and
fixed-fiber group geometry are constructed from the given family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] TangentBasePoint.fixedFamilyFiber
attribute [local instance] Abelian.Tangent.abelianFamilyFixedFiber_smooth Abelian.Tangent.abelianFamilyFixedFiber_proper
  Abelian.Tangent.abelianFamilyFixedFiber_connected Abelian.Tangent.abelianFamilyFixedFiber_integral FamilyTangent.IntrinsicVanishing.familyNativeFixedFiber_group

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    {g N : ℕ} {δ : Fin g → ℕ} (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))
    {I : Type} [Fintype I]
    (b : Module.Basis I ℂ (Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme)))

theorem polarizationGraphNativeCup_boundary (d : Derivation ℂ R ℂ) :
    let C := Constructed.LineFrameCover.lineBundleAffineFrameCover A.graphBundle
    Regular.BoundaryShuffle.RegularTripleBoundary (TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme).left
      (Fixed.CechCover.fixedFamilyCechCover ℂ R A.abelian.scheme C.cover)
      (Family.LineIntrinsicClass.familyLineLogRegularPair ℂ R A.abelian.scheme C.cover C.transitions d)
      (Family.LineTangentCupBoundary.familyLineTangentCupTriple R A.abelian.scheme C.cover C.transitions b d) :=
  Family.LineTangentCupBoundary.familyLineTangentCupTriple_boundary R A.abelian.scheme (Constructed.LineFrameCover.lineBundleAffineFrameCover A.graphBundle).cover
    (Constructed.LineFrameCover.lineBundleAffineFrameCover A.graphBundle).transitions b d

theorem polarizationGraphNativeCupClass_eq_zero (d : Derivation ℂ R ℂ) :
    let C := Constructed.LineFrameCover.lineBundleAffineFrameCover A.graphBundle
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (Fixed.CechCover.fixedFamilyCechCover ℂ R A.abelian.scheme C.cover)
      (Dual.UnitCechClasses.ringAdditiveSheaf (TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme).left.sheaf)
      (Fixed.CechCover.fixedFamilyCechCover_covers ℂ R A.abelian.scheme C.cover) 1
      (Regular.BoundaryShuffle.regularTripleCechCochain (TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme).left
        (Fixed.CechCover.fixedFamilyCechCover ℂ R A.abelian.scheme C.cover)
        (Family.LineTangentCupBoundary.familyLineTangentCupTriple R A.abelian.scheme C.cover C.transitions b d))
      (Regular.BoundaryShuffle.regularTripleCechCochain_closed (TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme).left
        (Fixed.CechCover.fixedFamilyCechCover ℂ R A.abelian.scheme C.cover)
        (Family.LineIntrinsicClass.familyLineLogRegularPair ℂ R A.abelian.scheme C.cover C.transitions d)
        (Family.LineTangentCupBoundary.familyLineTangentCupTriple R A.abelian.scheme C.cover C.transitions b d)
        (polarizationGraphNativeCup_boundary R A b d)) =
      (0 : (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology (TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme).left.toPresheafedSpace.carrier) 2).obj
          (Dual.UnitCechClasses.ringAdditiveSheaf (TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme).left.sheaf)) :=
  Family.LineTangentCupBoundary.familyLineTangentCupClass_eq_zero R A.abelian.scheme (Constructed.LineFrameCover.lineBundleAffineFrameCover A.graphBundle).cover
    (Constructed.LineFrameCover.lineBundleAffineFrameCover A.graphBundle).transitions b d

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.GraphIntrinsicCupConstraint
