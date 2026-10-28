import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.CoverCupTensor
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationGraphPairing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.GraphIntrinsicCupConstraint
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.TangentBilinear

/-! # Family Reference Cup Tensor -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FamilyReferenceCupTensor.Construction

noncomputable section

/-! The original polarized family cup boundary gives zero alternating
tensor of its actual tangent obstruction and graph logarithm. The
polarization pairing then gives twice the alternating coefficient tensor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] FixedFiber.IntrinsicChartRange.Construction.fixedTranslationProjectionAffine AbelianModuli.ReferenceFamily.Polarized.ConormalBilinear.polarizedPairingH1Module

attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullback
attribute [local instance] AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_smooth AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_proper
  AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_connected AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_integral AbelianModuli.ReferenceFamily.FamilyTangent.IntrinsicVanishing.familyNativeFixedFiber_group

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))
    (C : AbelianModuli.ReferenceFamily.Constructed.LineFrameCover.LineBundleAffineFrameCover A.graphBundle)
    {I : Type} [Fintype I]
    (b : Module.Basis I ℂ (AbelianModuli.ReferenceFamily.Constructed.IdentityConormal.constructedIdentityConormal ℂ (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme)))

local instance polarizedCupH1Module :
    Module ℂ (SheafCohomology.AffineH.Projective.H (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme).left) 1) :=
  AbelianModuli.ReferenceFamily.StructureComplexScalars.structureH1ComplexModule (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme)

theorem polarizedFamily_originalCupTensor (d : Derivation ℂ R ℂ) :
    ∑ a, (AbelianModuli.ReferenceFamily.Family.BaseTangentObstruction.familyTangentSheafClass R A.abelian.scheme C.cover d (b a) ⊗ₜ[ℂ]
      AbelianModuli.ReferenceFamily.FixedFiber.LineLogIntrinsicClass.fixedFiberLineLogSheafClass R A.abelian.scheme C.cover C.transitions (b.coord a) -
      AbelianModuli.ReferenceFamily.FixedFiber.LineLogIntrinsicClass.fixedFiberLineLogSheafClass R A.abelian.scheme C.cover C.transitions (b.coord a) ⊗ₜ[ℂ]
      AbelianModuli.ReferenceFamily.Family.BaseTangentObstruction.familyTangentSheafClass R A.abelian.scheme C.cover d (b a)) = 0 := by
  let A₀ := A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))
  let U := AbelianModuli.ReferenceFamily.Fixed.CechCover.fixedFamilyCechCover ℂ R A.abelian.scheme C.cover
  have hAffine (i : C.cover.I₀) : IsAffineOpen (U i) := by
    change IsAffineOpen (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFiberAffineOpen R ℂ A.abelian.scheme
      (AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverAffineOpen R A.abelian.scheme C.cover i))
    exact (AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverAffineOpen R A.abelian.scheme C.cover i).2.preimage
      (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ A.abelian.scheme)
  have hUU (i j : C.cover.I₀) : IsAffineOpen (U i ⊓ U j) := by
    rw [← AbelianModuli.ReferenceFamily.Fixed.CechCover.fixedFamilyCechCover_pair]
    exact (AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverPairAffineOpen R A.abelian.scheme C.cover i j).2.preimage
      (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ A.abelian.scheme)
  exact Reference.CoverCupTensor.Construction.originalCoverCup_alternatingTensor_eq_zero A₀.abelian A₀.dual
    (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A₀) U
    (AbelianModuli.ReferenceFamily.Fixed.CechCover.fixedFamilyCechCover_covers ℂ R A.abelian.scheme C.cover) hAffine hUU
    (fun a => AbelianModuli.ReferenceFamily.FamilyTangent.RegularCocycle.familyTangentRegularPair R A.abelian.scheme C.cover d (b a))
    (fun a => AbelianModuli.ReferenceFamily.FixedFiber.LineLogIntrinsicClass.fixedFiberLineLogRegularPair R A.abelian.scheme C.cover C.transitions (b.coord a))
    (fun a => AbelianModuli.ReferenceFamily.FamilyTangent.RegularCocycle.familyTangentRegularPair_cocycle R A.abelian.scheme C.cover d (b a))
    (fun a => AbelianModuli.ReferenceFamily.FixedFiber.LineLogIntrinsicClass.fixedFiberLineLogRegularPair_cocycle R A.abelian.scheme C.cover C.transitions (b.coord a))
    (AbelianModuli.ReferenceFamily.Family.LineIntrinsicClass.familyLineLogRegularPair ℂ R A.abelian.scheme C.cover C.transitions d)
    (AbelianModuli.ReferenceFamily.Family.LineTangentCupBoundary.familyLineTangentCupTriple_boundary R A.abelian.scheme C.cover C.transitions b d)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FamilyReferenceCupTensor.Construction
