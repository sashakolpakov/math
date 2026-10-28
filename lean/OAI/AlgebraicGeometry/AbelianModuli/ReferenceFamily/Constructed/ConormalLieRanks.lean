import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalIntegralAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Lie

/-! # Conormal Lie Ranks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The original Lie rank condition determines the character ranks
on the complex dual of the constructed conormal module. The comparison
is the actual native tangent/conormal equivalence with its proved action
pairing, not an additional representation hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {O : Type} [CommRing O] {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction O A) (τ : O →+* ℂ)

local instance Constructed.ConormalLieRanks.conormalLieRank_integral : IsIntegral A.scheme.left := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral A
attribute [local irreducible] Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear Constructed.ConormalIntegralAction.constructedConormalIntegralAction

def Constructed.ConormalLieRanks.constructedConormalDualEigenSpace : Submodule ℂ (Constructed.IdentityConormal.constructedIdentityConormal ℂ A.scheme →ₗ[ℂ] ℂ) where
  carrier := {l | ∀ a z, l (Constructed.ConormalIntegralAction.constructedConormalIntegralAction A ρ a z) = τ a * l z}
  zero_mem' := by intro a z; simp only [LinearMap.zero_apply, mul_zero]
  add_mem' hl hm a z := by
    simp only [LinearMap.add_apply, hl a z, hm a z, mul_add]
  smul_mem' c l hl a z := by
    change c * l (Constructed.ConormalIntegralAction.constructedConormalIntegralAction A ρ a z) = τ a * (c * l z)
    rw [hl]
    exact mul_left_comm c (τ a) (l z)

theorem Constructed.ConormalLieRanks.nativeIdentityConormal_eigen_iff
    (v : Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.scheme.hom) → ℂ) :
    Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A.scheme v ∈ Constructed.ConormalLieRanks.constructedConormalDualEigenSpace A ρ τ ↔
      v ∈ Intrinsic.Lie.nativeLieEigenspace A ρ τ := by
  constructor
  · intro h a
    apply (Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A.scheme).injective
    apply LinearMap.ext
    intro z
    rw [map_smul, LinearMap.smul_apply]
    exact (Constructed.ConormalIntegralAction.constructedConormalIntegralAction_pairing A ρ a v z).symm.trans (h a z)
  · intro h a z
    rw [Constructed.ConormalIntegralAction.constructedConormalIntegralAction_pairing, h a, map_smul, LinearMap.smul_apply]
    rfl

def Constructed.ConormalLieRanks.nativeConormalDualEigenEquiv : Intrinsic.Lie.nativeLieEigenspace A ρ τ ≃ₗ[ℂ] Constructed.ConormalLieRanks.constructedConormalDualEigenSpace A ρ τ where
  toFun v := ⟨Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A.scheme v.val, (Constructed.ConormalLieRanks.nativeIdentityConormal_eigen_iff A ρ τ v.val).mpr v.property⟩
  invFun l := ⟨(Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A.scheme).symm l.val, by
    apply (Constructed.ConormalLieRanks.nativeIdentityConormal_eigen_iff A ρ τ _).mp
    rw [LinearEquiv.apply_symm_apply]
    exact l.property⟩
  left_inv v := Subtype.ext ((Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A.scheme).symm_apply_apply v.val)
  right_inv l := Subtype.ext ((Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A.scheme).apply_symm_apply l.val)
  map_add' v w := Subtype.ext (map_add (Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A.scheme) v.val w.val)
  map_smul' c v := Subtype.ext (map_smul (Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A.scheme) c v.val)

theorem LieRanks.HasLieRank.constructedConormalDual_finrank {r : ℕ} (hr : LieRanks.HasLieRank A ρ τ r) :
    Module.finrank ℂ (Constructed.ConormalLieRanks.constructedConormalDualEigenSpace A ρ τ) = r :=
  (Constructed.ConormalLieRanks.nativeConormalDualEigenEquiv A ρ τ).finrank_eq.symm.trans (hr.native_finrank A ρ τ)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
