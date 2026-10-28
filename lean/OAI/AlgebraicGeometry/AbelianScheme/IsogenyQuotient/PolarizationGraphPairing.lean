import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationGraphLog
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.ConormalBilinear

/-! # Polarization Graph Pairing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationGraphPairing.Construction

noncomputable section

/-! Under the actual polarization pairing, the original graph-bundle
logarithm in a conormal direction is exactly twice that direction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.ConormalBilinear

attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullback
attribute [local instance] AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_smooth AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_proper
  AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_connected AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_integral AbelianModuli.ReferenceFamily.FamilyTangent.IntrinsicVanishing.familyNativeFixedFiber_group

variable (R : Type) [CommRing R] [Algebra R ℂ]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))
    (C : AbelianModuli.ReferenceFamily.Constructed.LineFrameCover.LineBundleAffineFrameCover A.graphBundle)

local instance graphPairingH1Module :
    Module ℂ (SheafCohomology.AffineH.Projective.H (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule
      (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).abelian.scheme.left) 1) :=
  AbelianModuli.ReferenceFamily.StructureComplexScalars.structureH1ComplexModule
    (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).abelian.scheme

theorem polarizationGraphLineLog_polarizedPairing
    (l : AbelianModuli.ReferenceFamily.Constructed.IdentityConormal.constructedIdentityConormal ℂ (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme) →ₗ[ℂ] ℂ) :
    AbelianModuli.ReferenceFamily.Polarized.ConormalBilinear.polarizedH1ConormalEquiv
      (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
      (AbelianModuli.ReferenceFamily.FixedFiber.LineLogIntrinsicClass.fixedFiberLineLogSheafClass R A.abelian.scheme C.cover C.transitions l) =
      (2 : ℂ) • l := by
  let G := AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme
  let A₀ := A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))
  let v := (AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear G).symm l
  have hv : AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear G v = l :=
    (AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear G).apply_symm_apply l
  have h := PolarizationGraphLog.Construction.polarizationGraphLineLogSheafClass_native R A C v
  rw [hv] at h
  rw [h, map_smul]
  change (2 : ℂ) • AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear G
    ((AbelianModuli.ReferenceFamily.Polarized.TangentEquiv.polarizedStructureH1TangentEquiv A₀).symm (AbelianModuli.ReferenceFamily.Polarized.TangentEquiv.polarizedStructureH1TangentEquiv A₀ v)) = _
  exact congrArg (fun z => (2 : ℂ) • z)
    ((congrArg (AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear G)
      ((AbelianModuli.ReferenceFamily.Polarized.TangentEquiv.polarizedStructureH1TangentEquiv A₀).symm_apply_apply v)).trans hv)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationGraphPairing.Construction
