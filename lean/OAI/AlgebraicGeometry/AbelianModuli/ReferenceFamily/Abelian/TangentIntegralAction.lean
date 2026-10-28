import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.SheafMorphism
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalIntegralAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.IntrinsicVanishing

/-! # Tangent Integral Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.TangentIntegralAction

noncomputable section

/-! The actual tangent obstruction of an abelian family intertwines
every original integral endomorphism with its constructed conormal
action and native structure-sheaf H1 pullback on the fixed fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] TangentBasePoint.fixedFamilyFiber HilbertConstruction.Abelian.Schemes.AbelianScheme.pullback
attribute [local irreducible] Intrinsic.GroupConormalMap.constructedConormalPullback Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear
attribute [local irreducible] Family.BaseTangentObstruction.familyTangentSheafClass StructurePullbackLinear.nativeStructureH1PullbackLinear
attribute [local instance] Tangent.abelianFamilyFixedFiber_smooth Tangent.abelianFamilyFixedFiber_proper
  Tangent.abelianFamilyFixedFiber_connected Tangent.abelianFamilyFixedFiber_integral FamilyTangent.IntrinsicVanishing.familyNativeFixedFiber_group

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    {O : Type} [CommRing O] {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of R)))
    (ρ : ActionData.IntegralAction O A) (U : Scheme.AffineOpenCover.{0, 0} A.scheme.left)

theorem abelianFamilyTangentSheafClass_integralAction (a : O) (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R A.scheme)) :
    Family.BaseTangentObstruction.familyTangentSheafClass R A.scheme U d
        (Constructed.ConormalIntegralAction.constructedConormalIntegralAction (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
          (ρ.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) a z) =
      StructurePullbackLinear.nativeStructureH1PullbackLinear
        ((ρ.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map a)
        (Family.BaseTangentObstruction.familyTangentSheafClass R A.scheme U d z) :=
  FamilyTangent.SheafMorphism.familyTangentSheafClass_morphism R (ρ.map a) U U d z

local instance abelianFamilyTangentH1_complexModule :
    Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule (TangentBasePoint.fixedFamilyFiber ℂ R A.scheme).left) 1) :=
  StructureComplexScalars.structureH1ComplexModule (TangentBasePoint.fixedFamilyFiber ℂ R A.scheme)

theorem abelianFamilyTangentObstruction_integralAction (a : O) (d : Derivation ℂ R ℂ) :
    (Family.BaseTangentObstruction.familyBaseTangentObstruction R A.scheme U d).comp
        (Constructed.ConormalIntegralAction.constructedConormalIntegralAction (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
          (ρ.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) a) =
      (StructurePullbackLinear.nativeStructureH1PullbackLinear
        ((ρ.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map a)).comp
        (Family.BaseTangentObstruction.familyBaseTangentObstruction R A.scheme U d) :=
  LinearMap.ext (abelianFamilyTangentSheafClass_integralAction R A ρ U a d)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.TangentIntegralAction
