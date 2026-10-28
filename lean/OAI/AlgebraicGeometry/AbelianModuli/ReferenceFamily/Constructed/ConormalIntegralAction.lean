import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalAddition
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.GroupConormalNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Lie

/-! # Conormal Integral Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalIntegralAction

noncomputable section

/-! The original integral action of an abelian scheme induces a
ring action on its constructed identity conormal module. Pairing with
native tangents and actual coefficient-valued lift coordinates recovers
the original group endomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {O : Type} [CommRing O] {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (ρ : ActionData.IntegralAction O A)

local instance conormalIntegralAction_integral : IsIntegral A.scheme.left := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral A
attribute [local irreducible] Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear

def constructedConormalIntegralAction : O →+* Module.End ℂ (IdentityConormal.constructedIdentityConormal ℂ A.scheme) where
  toFun a := Intrinsic.GroupConormalMap.constructedConormalPullback (ρ.map a)
  map_zero' := by rw [ρ.map_zero, ConormalAddition.constructedConormalPullback_one]
  map_one' := by rw [ρ.map_one, ConormalFunctoriality.constructedConormalPullback_id]; rfl
  map_add' a b := by rw [ρ.map_add, ConormalAddition.constructedConormalPullback_mul]
  map_mul' a b := by rw [mul_comm a b, ρ.map_mul, ConormalFunctoriality.constructedConormalPullback_comp]; rfl

theorem constructedConormalIntegralAction_pairing (a : O)
    (v : Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.scheme.hom) → ℂ)
    (z : IdentityConormal.constructedIdentityConormal ℂ A.scheme) :
    Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A.scheme v (constructedConormalIntegralAction A ρ a z) =
      Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A.scheme (Intrinsic.Lie.nativeLieDifferential A ρ a v) z := by
  change Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A.scheme v (Intrinsic.GroupConormalMap.constructedConormalPullback (ρ.map a) z) = _
  rw [Intrinsic.GroupConormalMap.constructedConormalPullback_pairing]
  change Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A.scheme
      (Intrinsic.GroupConormalMap.nativeGroupTangentMap (ρ.map a) ((Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A.scheme).symm
        (Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A.scheme v))) z = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem constructedConormalIntegralAction_lift (a : O)
    (C : Type) [CommRing C] [Algebra ℂ C] [Algebra.FiniteType ℂ C] [IsReduced C]
    (c : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber C) ⟶ A.scheme)
    (u : {u : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber C) ⟶ A.scheme // Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ u = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ c}) :
    IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A.scheme C (c ≫ ρ.map a)
        (Regular.GroupConormalNaturality.coefficientGroupPostcomposeLift (ρ.map a) C c u) =
      (IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A.scheme C c u).comp (constructedConormalIntegralAction A ρ a) :=
  Regular.GroupConormalNaturality.regularGroupConormal_natural (ρ.map a) C c u

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalIntegralAction
