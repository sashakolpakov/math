import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.SheafMorphism
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalFunctoriality

/-! # Family Tangent Cover Independence -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FamilyTangentCoverIndependence.Construction

noncomputable section

/-! The original family tangent H1 class is independent of the chosen
affine cover. Both comparisons use the actual identity family morphism;
its common pullback value cancels without a new compatibility premise. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (X : Over (Spec (.of R))) [Smooth X.hom] [IsSeparated X.hom]
    [IsIntegral (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)]
    (U V : Scheme.AffineOpenCover.{0, 0} X.left)

local instance rawFixedFiberIntegral : IsIntegral
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X).left :=
  inferInstanceAs (IsIntegral (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).left)
local instance rawFixedFiberSmooth : Smooth
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X).hom :=
  inferInstanceAs (Smooth (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).hom)
local instance rawFixedFiberGroup : GrpObj
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X) :=
  inferInstanceAs (GrpObj (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X))

local instance identityFixedFiberMonHom : IsMonHom
    (show AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X ⟶ AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X from
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map (𝟙 X)) := by
  rw [CategoryTheory.Functor.map_id]
  exact inferInstanceAs (IsMonHom (𝟙 (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)))

private theorem conormal_identity_apply (G : Over (Spec (.of ℂ)))
    [IsIntegral G.left] [Smooth G.hom] [GrpObj G]
    (z : AbelianModuli.ReferenceFamily.Constructed.IdentityConormal.constructedIdentityConormal ℂ G) :
    AbelianModuli.ReferenceFamily.Intrinsic.GroupConormalMap.constructedConormalPullback (𝟙 G) z = z :=
  LinearMap.congr_fun (AbelianModuli.ReferenceFamily.Constructed.ConormalFunctoriality.constructedConormalPullback_id G) z

private theorem change_argument {A B : Type*} (f g : A → B)
    {x y : A} (hxy : x = y) (h : f x = g x) : f y = g y := by
  cases hxy
  exact h

theorem familyTangentSheafClass_cover_independent (d : Derivation ℂ R ℂ)
    (z : AbelianModuli.ReferenceFamily.Constructed.IdentityConormal.constructedIdentityConormal ℂ (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)) :
    AbelianModuli.ReferenceFamily.Family.BaseTangentObstruction.familyTangentSheafClass R X U d z = AbelianModuli.ReferenceFamily.Family.BaseTangentObstruction.familyTangentSheafClass R X V d z := by
  have hUV := AbelianModuli.ReferenceFamily.FamilyTangent.SheafMorphism.familyTangentSheafClass_morphism R (𝟙 X) U V d z
  have hVV := AbelianModuli.ReferenceFamily.FamilyTangent.SheafMorphism.familyTangentSheafClass_morphism R (𝟙 X) V V d z
  have hid : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map (𝟙 X) =
      𝟙 (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X) := CategoryTheory.Functor.map_id _ _
  have hc : AbelianModuli.ReferenceFamily.Intrinsic.GroupConormalMap.constructedConormalPullback ((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap R ℂ)))).map (𝟙 X)) z = z := by
    rw [hid]
    have h := conormal_identity_apply (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X) z
    convert h using 2
  have hcommon : AbelianModuli.ReferenceFamily.Family.BaseTangentObstruction.familyTangentSheafClass R X U d
      (AbelianModuli.ReferenceFamily.Intrinsic.GroupConormalMap.constructedConormalPullback ((Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap R ℂ)))).map (𝟙 X)) z) =
      AbelianModuli.ReferenceFamily.Family.BaseTangentObstruction.familyTangentSheafClass R X V d
      (AbelianModuli.ReferenceFamily.Intrinsic.GroupConormalMap.constructedConormalPullback ((Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap R ℂ)))).map (𝟙 X)) z) := by
    refine Eq.trans (b := AbelianModuli.ReferenceFamily.StructurePullbackLinear.nativeStructureH1PullbackLinear
      (show AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X ⟶ AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X from
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map (𝟙 X))
        (AbelianModuli.ReferenceFamily.Family.BaseTangentObstruction.familyTangentSheafClass R X V d z)) ?_ ?_
    · convert hUV using 2
    · have hrev := hVV.symm
      convert hrev using 2
  have result := change_argument (AbelianModuli.ReferenceFamily.Family.BaseTangentObstruction.familyTangentSheafClass R X U d)
    (AbelianModuli.ReferenceFamily.Family.BaseTangentObstruction.familyTangentSheafClass R X V d) hc hcommon
  convert result using 2

local instance coverIndependentH1Module :
    Module ℂ (SheafCohomology.AffineH.Projective.H (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).left) 1) :=
  AbelianModuli.ReferenceFamily.StructureComplexScalars.structureH1ComplexModule (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)

theorem familyBaseTangentObstruction_cover_independent :
    AbelianModuli.ReferenceFamily.Family.BaseTangentObstruction.familyBaseTangentObstruction R X U = AbelianModuli.ReferenceFamily.Family.BaseTangentObstruction.familyBaseTangentObstruction R X V := by
  apply LinearMap.ext
  intro d
  exact LinearMap.ext (familyTangentSheafClass_cover_independent R X U V d)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FamilyTangentCoverIndependence.Construction
