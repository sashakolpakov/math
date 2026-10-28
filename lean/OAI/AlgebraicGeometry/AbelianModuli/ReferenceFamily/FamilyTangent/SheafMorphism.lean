import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.SheafMorphismOnCover
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.MorphismCompatibleAffineCover

/-! # Sheaf Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.SheafMorphism

noncomputable section

/-! Actual family morphisms induce the expected naturality of the
original tangent obstruction in native structure-sheaf H1. Compatible
affine refinements are constructed from the two original covers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    {X Y : Over (Spec (.of R))} [Smooth X.hom] [Smooth Y.hom]
    [IsSeparated X.hom] [IsSeparated Y.hom]
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R X)]
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R Y).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R Y).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R Y)]
    (f : X ⟶ Y)
    [IsMonHom (show TangentBasePoint.fixedFamilyFiber ℂ R X ⟶ TangentBasePoint.fixedFamilyFiber ℂ R Y from
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f)]
    (U : Scheme.AffineOpenCover.{0, 0} X.left) (V : Scheme.AffineOpenCover.{0, 0} Y.left)

theorem familyTangentSheafClass_morphism (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R Y)) :
    Family.BaseTangentObstruction.familyTangentSheafClass R X U d
        (Intrinsic.GroupConormalMap.constructedConormalPullback (show TangentBasePoint.fixedFamilyFiber ℂ R X ⟶ TangentBasePoint.fixedFamilyFiber ℂ R Y from
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f) z) =
      StructurePullbackLinear.nativeStructureH1PullbackLinear (show TangentBasePoint.fixedFamilyFiber ℂ R X ⟶ TangentBasePoint.fixedFamilyFiber ℂ R Y from
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f)
        (Family.BaseTangentObstruction.familyTangentSheafClass R Y V d z) := by
  let D := MorphismCompatibleAffineCover.morphismCompatibleAffineCover f.left U V
  let r : D.I₀ → U.I₀ := fun i => (show MorphismCompatibleAffineCover.MorphismAffineRefinementIndex f.left U V from i).source
  let s : D.I₀ → V.I₀ := fun i => (show MorphismCompatibleAffineCover.MorphismAffineRefinementIndex f.left U V from i).target
  have hr (i : D.I₀) : (Family.AffineCoverIntersections.familyCoverAffineOpen R X D i).1 ≤ (Family.AffineCoverIntersections.familyCoverAffineOpen R X U (r i)).1 :=
    MorphismCompatibleAffineCover.morphismCompatibleAffineCover_source f.left U V i
  have hs (i : D.I₀) : (Family.AffineCoverIntersections.familyCoverAffineOpen R X D i).1 ≤ f.left ⁻¹ᵁ (Family.AffineCoverIntersections.familyCoverAffineOpen R Y V (s i)).1 :=
    MorphismCompatibleAffineCover.morphismCompatibleAffineCover_target f.left U V i
  exact SheafMorphismOnCover.familyTangentSheafClass_morphism_onCover R f D U V r s hr hs d z

local instance familyTangentMorphismH1_complexModule (A : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.left) 1) := StructureComplexScalars.structureH1ComplexModule A

theorem familyBaseTangentObstruction_morphism (d : Derivation ℂ R ℂ) :
    (Family.BaseTangentObstruction.familyBaseTangentObstruction R X U d).comp
        (Intrinsic.GroupConormalMap.constructedConormalPullback (show TangentBasePoint.fixedFamilyFiber ℂ R X ⟶ TangentBasePoint.fixedFamilyFiber ℂ R Y from
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f)) =
      (StructurePullbackLinear.nativeStructureH1PullbackLinear (show TangentBasePoint.fixedFamilyFiber ℂ R X ⟶ TangentBasePoint.fixedFamilyFiber ℂ R Y from
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f)).comp
        (Family.BaseTangentObstruction.familyBaseTangentObstruction R Y V d) :=
  LinearMap.ext (familyTangentSheafClass_morphism R f U V d)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.SheafMorphism
