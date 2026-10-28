import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.PicardLog
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.LineLogIntrinsicClass

/-! # Picard Pair Class -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.PicardPairClass.Construction

noncomputable section

section

/-! The actual native Picard coefficients on original family pair
overlaps form a closed regular cocycle and give the original line-log H1
class. The comparison with the globally represented translation line
class still requires the original cover/finite-intersection comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.LineLogIntrinsicClass

attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverAffineOpen AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverPairAffineOpen
attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.Fixed.CechCover.fixedFamilyCechCover AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFiberAffineOpen

variable (R : Type) [CommRing R] [Algebra R ℂ] (X : Over (Spec (.of R))) [IsSeparated X.hom]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (C : AbelianModuli.ReferenceFamily.Constructed.LineFrameCover.LineBundleAffineFrameCover L)
    [IsIntegral (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)]
    (v : Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).hom) → ℂ)

def fixedFiberNativePicardPair (i j : C.cover.I₀) :
    Γ((AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).left,
      AbelianModuli.ReferenceFamily.Fixed.CechCover.fixedFamilyCechCover ℂ R X C.cover i ⊓ AbelianModuli.ReferenceFamily.Fixed.CechCover.fixedFamilyCechCover ℂ R X C.cover j) :=
  PicardLog.Construction.fixedFiberPicardLogSection R X L C (AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverPairAffineOpen R X C.cover i j)
    i j inf_le_left inf_le_right v

include R X L C v in
abbrev fixedFiberNativePicardPair_eq_log :=
  funext (fun i => funext (fun j => PicardLog.Construction.fixedFiberPicardLogSection_eq R X L C
    (AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverPairAffineOpen R X C.cover i j) i j inf_le_left inf_le_right v))

theorem regularPairSheafClass_eq_of_pairs_eq
    (S : Scheme.{0}) {I : Type} (U : I → S.Opens) (hU : iSup U = ⊤)
    {a b : ∀ i j : I, Γ(S, U i ⊓ U j)}
    (ha : AbelianModuli.ReferenceFamily.RegularPair.Closed.RegularPairCocycle S U a) (hb : AbelianModuli.ReferenceFamily.RegularPair.Closed.RegularPairCocycle S U b) (hab : a = b) :
    AbelianModuli.ReferenceFamily.RegularPair.Closed.regularPairSheafClass S U hU a ha = AbelianModuli.ReferenceFamily.RegularPair.Closed.regularPairSheafClass S U hU b hb := by
  cases hab
  rfl

include R X L C v in
abbrev fixedFiberNativePicardPair_cocycle := by
  have h := AbelianModuli.ReferenceFamily.FixedFiber.LineLogIntrinsicClass.fixedFiberLineLogRegularPair_cocycle R X C.cover C.transitions
    (AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X) v)
  exact (congrArg (AbelianModuli.ReferenceFamily.RegularPair.Closed.RegularPairCocycle (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).left
    (AbelianModuli.ReferenceFamily.Fixed.CechCover.fixedFamilyCechCover ℂ R X C.cover)) (fixedFiberNativePicardPair_eq_log R X L C v)).mpr h

end

/-! The actual native Picard coefficients on original family pair
overlaps form a closed regular cocycle and give the original line-log H1
class. The comparison with the globally represented translation line
class still requires the original cover/finite-intersection comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.LineLogIntrinsicClass

attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverAffineOpen AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverPairAffineOpen
attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.Fixed.CechCover.fixedFamilyCechCover AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFiberAffineOpen

variable (R : Type) [CommRing R] [Algebra R ℂ] (X : Over (Spec (.of R))) [IsSeparated X.hom]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (C : AbelianModuli.ReferenceFamily.Constructed.LineFrameCover.LineBundleAffineFrameCover L)
    [IsIntegral (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)]
    (v : Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).hom) → ℂ)

/-- Use the equivalent logarithmic cocycle to construct the same native class. -/
def fixedFiberNativePicardPairClass :
    SheafCohomology.AffineH.Projective.H (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).left) 1 :=
  AbelianModuli.ReferenceFamily.FixedFiber.LineLogIntrinsicClass.fixedFiberLineLogSheafClass R X C.cover C.transitions
    (AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X) v)

theorem fixedFiberNativePicardPairClass_eq_log :
    fixedFiberNativePicardPairClass R X L C v =
      AbelianModuli.ReferenceFamily.FixedFiber.LineLogIntrinsicClass.fixedFiberLineLogSheafClass R X C.cover C.transitions
        (AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X) v) := rfl

/- The logarithmic representative equals the class of the proved native coefficient cocycle. -/
include R X L C v in
abbrev fixedFiberNativePicardPairClass_eq_native :=
  (regularPairSheafClass_eq_of_pairs_eq (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).left
    (AbelianModuli.ReferenceFamily.Fixed.CechCover.fixedFamilyCechCover ℂ R X C.cover) (AbelianModuli.ReferenceFamily.Fixed.CechCover.fixedFamilyCechCover_covers ℂ R X C.cover)
    (fixedFiberNativePicardPair_cocycle R X L C v)
    (AbelianModuli.ReferenceFamily.FixedFiber.LineLogIntrinsicClass.fixedFiberLineLogRegularPair_cocycle R X C.cover C.transitions
      (AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X) v))
    (fixedFiberNativePicardPair_eq_log R X L C v)).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.PicardPairClass.Construction
