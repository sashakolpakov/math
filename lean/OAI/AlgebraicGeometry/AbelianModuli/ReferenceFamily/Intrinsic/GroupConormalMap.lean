import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeDualNaturality
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Group Conormal Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.GroupConormalMap

noncomputable section

/-! An actual morphism of smooth integral complex groups induces
the native tangent map and its contravariant map on the constructed
identity conormal spaces. The pairing formula retains the original
native differential. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable {A B : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral A.left] [Smooth A.hom] [GrpObj A]
    [IsIntegral B.left] [Smooth B.hom] [GrpObj B] (f : A ⟶ B)

local notation "ModelA" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.hom) → ℂ)
local notation "ModelB" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension B.hom) → ℂ)

def nativeGroupTangentMap : ModelA →ₗ[ℂ] ModelB :=
  (mfderiv 𝓘(ℂ, ModelA) 𝓘(ℂ, ModelB) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) 1).toLinearMap

theorem nativeGroupTangentMap_lift [IsMonHom f] (v : ModelA) :
    (SchemeDualTangent.nativeSchemeTangentDualEquiv B 1 (nativeGroupTangentMap f v)).val =
      (SchemeDualTangent.nativeSchemeTangentDualEquiv A 1 v).val ≫ f := by
  have hn := SchemeDualNaturality.nativeSchemeTangentDual_natural f 1 v
  have hp : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f 1 = (1 : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B) := MonObj.one_comp f
  have he := congrArg (fun p => (SchemeDualTangent.nativeSchemeTangentDualEquiv B p (nativeGroupTangentMap f v)).val) hp
  exact he.symm.trans hn

def nativeConormalDualMap :
    (Constructed.IdentityConormal.constructedIdentityConormal ℂ A →ₗ[ℂ] ℂ) →ₗ[ℂ] (Constructed.IdentityConormal.constructedIdentityConormal ℂ B →ₗ[ℂ] ℂ) :=
  (IdentityConormalLinear.nativeIdentityConormalLinear B).toLinearMap.comp
    ((nativeGroupTangentMap f).comp (IdentityConormalLinear.nativeIdentityConormalLinear A).symm.toLinearMap)

def constructedConormalPullback : Constructed.IdentityConormal.constructedIdentityConormal ℂ B →ₗ[ℂ] Constructed.IdentityConormal.constructedIdentityConormal ℂ A :=
  (Module.evalEquiv ℂ (Constructed.IdentityConormal.constructedIdentityConormal ℂ A)).symm.toLinearMap.comp
    ((nativeConormalDualMap f).dualMap.comp (Module.evalEquiv ℂ (Constructed.IdentityConormal.constructedIdentityConormal ℂ B)).toLinearMap)

theorem constructedConormalPullback_pairing
    (l : Constructed.IdentityConormal.constructedIdentityConormal ℂ A →ₗ[ℂ] ℂ) (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ B) :
    l (constructedConormalPullback f z) = nativeConormalDualMap f l z := by
  exact Module.apply_evalEquiv_symm_apply ℂ (Constructed.IdentityConormal.constructedIdentityConormal ℂ A) l
    ((nativeConormalDualMap f).dualMap (Module.evalEquiv ℂ (Constructed.IdentityConormal.constructedIdentityConormal ℂ B) z))

theorem nativeConormalDualMap_pairing
    (l : Constructed.IdentityConormal.constructedIdentityConormal ℂ A →ₗ[ℂ] ℂ) :
    nativeConormalDualMap f l = l.comp (constructedConormalPullback f) := by
  apply LinearMap.ext
  intro z
  exact (constructedConormalPullback_pairing f l z).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.GroupConormalMap
