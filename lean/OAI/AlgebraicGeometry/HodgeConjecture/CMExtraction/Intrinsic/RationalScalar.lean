import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SourceLevel
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActionProductScalar

/-! # Rational Scalar -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalScalar

noncomputable section

/-! Rational covariance uses exactly the away scalar when the active factor fixes the same test. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActionProductScalar.TestTransport

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hμ : D.pel.reference.μ = E.val.toRingHom)
  (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Multiplicity.nativeTensorPairing E D.pel.reference v x y))
  {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (u : MpF)
  (hu : FiniteDilation.NativeFiniteCoordinateIdentity E D e u)

theorem native_rational_action_scalar (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3))
    (hfixed : φ ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q)
      (CoordinateDualHecke.Local.coordinateDualRepresentation q c D.pel.reference.distinguished D.weil u))
    (γ : D.RationalSU)
    (hγ : LocalSymplectic.nativeLocalUnitaryBlocks E D γ D.pel.reference.distinguished ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q)
    (a : ℂ)
    (ha : D.weil.finite.action (RepresentationTheory.Hecke.BlockResidual.SphericalActionIntrinsic.activeResidual E D hg hμ v hv e he c u hu γ) φ = a • φ) :
    D.weil.finite.action (RationalSplitting.nativeRationalFiniteSplitting E D.pel.reference
      hg.reference_admissible hμ v hv e he D.weil γ) φ = a • φ :=
  ActionProductScalar.TestTransport.action_product_scalar D.weil.finite.action
    (CoordinateDualHecke.Local.coordinateDualLift q c D.pel.reference.distinguished D.weil u
      (LocalSymplectic.nativeLocalUnitaryBlocks E D γ D.pel.reference.distinguished))
    (RepresentationTheory.Hecke.BlockResidual.SphericalActionIntrinsic.activeResidual E D hg hμ v hv e he c u hu γ) _
    (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeSplitting_rational E D hg hμ v hv e he c u hu γ) φ a
    (hfixed _ hγ) ha

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalScalar
