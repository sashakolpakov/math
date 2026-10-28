import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TranslatedConormal
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeDualAddition

/-! # Conormal Cocycle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.ConormalCocycle

noncomputable section

/-! Changing the reference lift adds the actual conormal differences.
This is the torsor cocycle law for the original complex dual-number maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver LieRanks.dualNumberTest
attribute [local irreducible] Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear

variable (A : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral A.left] [Smooth A.hom] [GrpObj A]

theorem complexConormalCoordinate_recovery (c : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ A)
    (u : {u : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ ℂ ≫ u = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ ℂ ≫ c}) :
    (show EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ A from
      (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv A 1 ((Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A).symm
        (Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A ℂ c u))).val) * c = u.val := by
  have h := Intrinsic.TranslatedConormal.constructedIdentityLiftConormalEquiv_native_inverse A
    ((Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A).symm (Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A ℂ c u)) c
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm.trans (congrArg Subtype.val ((Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A ℂ c).symm_apply_apply u))

theorem complexConormalReference_cocycle (a b c : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ A)
    (hab : Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ ℂ ≫ b = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ ℂ ≫ a)
    (hbc : Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ ℂ ≫ c = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ ℂ ≫ b) :
    Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A ℂ a ⟨b, hab⟩ +
        Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A ℂ b ⟨c, hbc⟩ =
      Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A ℂ a ⟨c, hbc.trans hab⟩ := by
  let x := Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A ℂ a ⟨b, hab⟩
  let y := Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A ℂ b ⟨c, hbc⟩
  let vx := (Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A).symm x
  let vy := (Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A).symm y
  have he : Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A (vy + vx) = x + y := by
    rw [map_add, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, add_comm]
  have h := Intrinsic.TranslatedConormal.constructedIdentityLiftConormalEquiv_native_inverse A (vy + vx) a
  rw [he] at h
  have ha := complexConormalCoordinate_recovery A a ⟨b, hab⟩
  have hb := complexConormalCoordinate_recovery A b ⟨c, hbc⟩
  have hv := SchemeDualAddition.nativeSchemeTangentDual_add A vy vx
  have hm : (show EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ A from
      (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv A 1 (vy + vx)).val) * a = c := by
    rw [hv, mul_assoc, ha]
    exact hb
  apply (Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A ℂ a).symm.injective
  apply Subtype.ext
  exact (h.trans hm).trans (congrArg Subtype.val
    ((Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A ℂ a).symm_apply_apply ⟨c, hbc.trans hab⟩)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.ConormalCocycle
