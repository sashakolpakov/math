import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.RegularCocycle
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.ClassAddition
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.ClassScalars
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructureComplexScalars

/-! # Base Tangent Obstruction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.BaseTangentObstruction

noncomputable section

/-! The actual affine tangent cocycle defines a complex-linear map
from base tangent vectors to native structure-sheaf H1 valued in the
dual of the fixed fiber's identity conormal module. Both variables retain
their original complex scalar actions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (X : Over (Spec (.of R))) [Smooth X.hom] [IsSeparated X.hom]
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R X)] (U : X.left.AffineOpenCover)

local instance familyTangentH1_complexModule :
    Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule (TangentBasePoint.fixedFamilyFiber ℂ R X).left) 1) :=
  StructureComplexScalars.structureH1ComplexModule (TangentBasePoint.fixedFamilyFiber ℂ R X)

def familyTangentSheafClass (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X)) :
    SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule (TangentBasePoint.fixedFamilyFiber ℂ R X).left) 1 :=
  RegularPair.Closed.regularPairSheafClass (TangentBasePoint.fixedFamilyFiber ℂ R X).left (Fixed.CechCover.fixedFamilyCechCover ℂ R X U)
    (Fixed.CechCover.fixedFamilyCechCover_covers ℂ R X U) (FamilyTangent.RegularCocycle.familyTangentRegularPair R X U d z)
    (FamilyTangent.RegularCocycle.familyTangentRegularPair_cocycle R X U d z)

theorem familyTangentSheafClass_add_tangent (d e : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X)) :
    familyTangentSheafClass R X U (d + e) z =
      familyTangentSheafClass R X U d z + familyTangentSheafClass R X U e z := by
  let v := FamilyTangent.RegularCocycle.familyTangentRegularPair R X U d z
  let w := FamilyTangent.RegularCocycle.familyTangentRegularPair R X U e z
  have hv := FamilyTangent.RegularCocycle.familyTangentRegularPair_cocycle R X U d z
  have hw := FamilyTangent.RegularCocycle.familyTangentRegularPair_cocycle R X U e z
  have he : FamilyTangent.RegularCocycle.familyTangentRegularPair R X U (d + e) z = (fun i j => v i j + w i j) :=
    funext (fun i => funext (fun j => FamilyTangent.RegularCocycle.familyTangentRegularPair_add_tangent R X U d e z i j))
  exact (RegularPair.ClassAddition.regularPairSheafClass_congr (TangentBasePoint.fixedFamilyFiber ℂ R X).left (Fixed.CechCover.fixedFamilyCechCover ℂ R X U)
    _ _ (Fixed.CechCover.fixedFamilyCechCover_covers ℂ R X U) (FamilyTangent.RegularCocycle.familyTangentRegularPair_cocycle R X U (d + e) z)
    (RegularPair.ClassAddition.regularPairCocycle_add (TangentBasePoint.fixedFamilyFiber ℂ R X).left (Fixed.CechCover.fixedFamilyCechCover ℂ R X U) v w hv hw) he).trans
      (RegularPair.ClassAddition.regularPairSheafClass_add (TangentBasePoint.fixedFamilyFiber ℂ R X).left (Fixed.CechCover.fixedFamilyCechCover ℂ R X U)
        v w (Fixed.CechCover.fixedFamilyCechCover_covers ℂ R X U) hv hw)

theorem familyTangentSheafClass_add_conormal (d : Derivation ℂ R ℂ)
    (z w : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X)) :
    familyTangentSheafClass R X U d (z + w) =
      familyTangentSheafClass R X U d z + familyTangentSheafClass R X U d w := by
  let v := FamilyTangent.RegularCocycle.familyTangentRegularPair R X U d z
  let v' := FamilyTangent.RegularCocycle.familyTangentRegularPair R X U d w
  have hv := FamilyTangent.RegularCocycle.familyTangentRegularPair_cocycle R X U d z
  have hv' := FamilyTangent.RegularCocycle.familyTangentRegularPair_cocycle R X U d w
  have he : FamilyTangent.RegularCocycle.familyTangentRegularPair R X U d (z + w) = (fun i j => v i j + v' i j) :=
    funext (fun i => funext (fun j => FamilyTangent.RegularCocycle.familyTangentRegularPair_add_conormal R X U d z w i j))
  exact (RegularPair.ClassAddition.regularPairSheafClass_congr (TangentBasePoint.fixedFamilyFiber ℂ R X).left (Fixed.CechCover.fixedFamilyCechCover ℂ R X U)
    _ _ (Fixed.CechCover.fixedFamilyCechCover_covers ℂ R X U) (FamilyTangent.RegularCocycle.familyTangentRegularPair_cocycle R X U d (z + w))
    (RegularPair.ClassAddition.regularPairCocycle_add (TangentBasePoint.fixedFamilyFiber ℂ R X).left (Fixed.CechCover.fixedFamilyCechCover ℂ R X U) v v' hv hv') he).trans
      (RegularPair.ClassAddition.regularPairSheafClass_add (TangentBasePoint.fixedFamilyFiber ℂ R X).left (Fixed.CechCover.fixedFamilyCechCover ℂ R X U)
        v v' (Fixed.CechCover.fixedFamilyCechCover_covers ℂ R X U) hv hv')

theorem familyTangentSheafClass_smul_tangent (c : ℂ) (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X)) :
    familyTangentSheafClass R X U (c • d) z = c • familyTangentSheafClass R X U d z :=
  RegularPair.ClassScalars.regularPairSheafClass_globalScalar (TangentBasePoint.fixedFamilyFiber ℂ R X).left (Fixed.CechCover.fixedFamilyCechCover ℂ R X U)
    (Fixed.CechCover.fixedFamilyCechCover_covers ℂ R X U) (FamilyTangent.RegularCocycle.familyTangentRegularPair R X U d z)
    (FamilyTangent.RegularCocycle.familyTangentRegularPair R X U (c • d) z) (FamilyTangent.RegularCocycle.familyTangentRegularPair_cocycle R X U d z)
    (FamilyTangent.RegularCocycle.familyTangentRegularPair_cocycle R X U (c • d) z) (Open.ComplexConstants.complexGlobalSectionMap (TangentBasePoint.fixedFamilyFiber ℂ R X) c)
    (FamilyTangent.RegularCocycle.familyTangentRegularPair_smul_tangent R X U c d z)

theorem familyTangentSheafClass_smul_conormal (c : ℂ) (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X)) :
    familyTangentSheafClass R X U d (c • z) = c • familyTangentSheafClass R X U d z :=
  RegularPair.ClassScalars.regularPairSheafClass_globalScalar (TangentBasePoint.fixedFamilyFiber ℂ R X).left (Fixed.CechCover.fixedFamilyCechCover ℂ R X U)
    (Fixed.CechCover.fixedFamilyCechCover_covers ℂ R X U) (FamilyTangent.RegularCocycle.familyTangentRegularPair R X U d z)
    (FamilyTangent.RegularCocycle.familyTangentRegularPair R X U d (c • z)) (FamilyTangent.RegularCocycle.familyTangentRegularPair_cocycle R X U d z)
    (FamilyTangent.RegularCocycle.familyTangentRegularPair_cocycle R X U d (c • z)) (Open.ComplexConstants.complexGlobalSectionMap (TangentBasePoint.fixedFamilyFiber ℂ R X) c)
    (FamilyTangent.RegularCocycle.familyTangentRegularPair_smul_conormal R X U c d z)

def familyTangentConormalObstruction (d : Derivation ℂ R ℂ) :
    Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X) →ₗ[ℂ]
      SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule (TangentBasePoint.fixedFamilyFiber ℂ R X).left) 1 where
  toFun := familyTangentSheafClass R X U d
  map_add' := familyTangentSheafClass_add_conormal R X U d
  map_smul' c z := familyTangentSheafClass_smul_conormal R X U c d z

def familyBaseTangentObstruction : Derivation ℂ R ℂ →ₗ[ℂ]
    (Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X) →ₗ[ℂ]
      SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule (TangentBasePoint.fixedFamilyFiber ℂ R X).left) 1) where
  toFun := familyTangentConormalObstruction R X U
  map_add' d e := LinearMap.ext (familyTangentSheafClass_add_tangent R X U d e)
  map_smul' c d := LinearMap.ext (familyTangentSheafClass_smul_tangent R X U c d)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.BaseTangentObstruction
