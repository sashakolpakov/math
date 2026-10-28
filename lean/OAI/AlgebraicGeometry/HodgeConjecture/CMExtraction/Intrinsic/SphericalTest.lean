import OAI.RepresentationTheory.Hecke.IntrinsicDatum

/-! # Spherical Test -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SphericalTest

noncomputable section

/-! The same test fixed by both actual factors belongs to the native spherical input space. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

open OAI.RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic

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

theorem native_spherical_mem (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3))
    (hlocal : φ ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q)
      (CoordinateDualHecke.Local.coordinateDualRepresentation q c D.pel.reference.distinguished D.weil u))
    [TopologicalSpace (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu)]
    (L : OpenSubgroup (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu))
    (haway : ∀ a ∈ L, D.weil.finite.action a.val φ = φ) :
    φ ∈ (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L).sphericalInputs := by
  intro g hg
  change D.weil.finite.action
    (CoordinateDualHecke.Local.coordinateDualLift q c D.pel.reference.distinguished D.weil u g.1 * g.2.val) φ = φ
  rw [map_mul, LinearEquiv.mul_apply, haway g.2 hg.2]
  exact hlocal g.1 hg.1

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SphericalTest
