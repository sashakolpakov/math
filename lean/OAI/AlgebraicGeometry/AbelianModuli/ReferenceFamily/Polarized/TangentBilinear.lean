import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.ConormalBilinear
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.TangentIntegralAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RosatiBaseChange

/-! # Tangent Bilinear -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.TangentBilinear

noncomputable section

/-! The actual base-tangent obstruction of a polarized family gives
a bilinear form on the original fixed-fiber conormal. The original CM
action satisfies its conjugate balancing identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] TangentBasePoint.fixedFamilyFiber HilbertConstruction.Abelian.Schemes.AbelianScheme.pullback
attribute [local irreducible] Intrinsic.GroupConormalMap.constructedConormalPullback Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear
attribute [local irreducible] Constructed.ConormalIntegralAction.constructedConormalIntegralAction StructurePullbackLinear.nativeStructureH1PullbackLinear
attribute [local instance] Abelian.Tangent.abelianFamilyFixedFiber_smooth Abelian.Tangent.abelianFamilyFixedFiber_proper
  Abelian.Tangent.abelianFamilyFixedFiber_connected Abelian.Tangent.abelianFamilyFixedFiber_integral FamilyTangent.IntrinsicVanishing.familyNativeFixedFiber_group

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    {g N : ℕ} {δ : Fin g → ℕ} (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))
    (U : Scheme.AffineOpenCover.{0, 0} A.abelian.scheme.left)

local instance polarizedFamilyH1Module :
    Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule (TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme).left) 1) :=
  StructureComplexScalars.structureH1ComplexModule (TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme)

def polarizedFamilyTangentBilinear : Derivation ℂ R ℂ →ₗ[ℂ]
    (Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme) →ₗ[ℂ]
      Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme) →ₗ[ℂ] ℂ) :=
  (ConormalBilinear.polarizedConormalBilinearLinear (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))).comp
    (Family.BaseTangentObstruction.familyBaseTangentObstruction R A.abelian.scheme U)

theorem polarizedFamilyTangentBilinear_eq_iff (d e : Derivation ℂ R ℂ) :
    polarizedFamilyTangentBilinear R A U d = polarizedFamilyTangentBilinear R A U e ↔
      Family.BaseTangentObstruction.familyBaseTangentObstruction R A.abelian.scheme U d =
        Family.BaseTangentObstruction.familyBaseTangentObstruction R A.abelian.scheme U e :=
  (ConormalBilinear.polarizedConormalBilinear_injective (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))).eq_iff

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian) (hρ : ActionData.RosatiConjugation A ρ)

include hρ

theorem polarizedFamilyTangentBilinear_balanced (a : NumberField.RingOfIntegers E) (d : Derivation ℂ R ℂ)
    (z w : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme)) :
    polarizedFamilyTangentBilinear R A U d
        (Constructed.ConormalIntegralAction.constructedConormalIntegralAction (A.abelian.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
          (ρ.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) a z) w =
      polarizedFamilyTangentBilinear R A U d z
        (Constructed.ConormalIntegralAction.constructedConormalIntegralAction (A.abelian.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
          (ρ.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
            (NumberField.IsCMField.ringOfIntegersComplexConj E a) w) :=
  ConormalBilinear.polarizedConormalBilinear_balanced (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
    (ρ.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
    (hρ.pullback A ρ (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
    (Family.BaseTangentObstruction.familyBaseTangentObstruction R A.abelian.scheme U d)
    (fun a => Abelian.TangentIntegralAction.abelianFamilyTangentObstruction_integralAction R A.abelian ρ U a d) a z w

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.TangentBilinear
