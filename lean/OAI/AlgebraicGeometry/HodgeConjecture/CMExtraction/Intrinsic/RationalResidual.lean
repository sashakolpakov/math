import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FiniteResidual
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalSplitting
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.Sl

/-! # Rational Residual -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalResidual

noncomputable section

/-! The away residual of the constructed rational SU splitting is an
actual homomorphism. Its projection is trivial at q and it commutes with
the entire local block family in the finite cover. -/

open scoped Classical _root_.Matrix

namespace Local

theorem blockFamilyFiniteLift_commute_of_trivial_projection
    (q : ℕ) [Fact q.Prime] {Place : Type} [Fintype Place] [DecidableEq Place]
    {n : ℕ} (c : (Place × Fin 3) ≃ Fin n)
    {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA) (m : MpF)
    (hm : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom (D.finite.project m) = 1) :
    ∀ g, Commute m (BlockFamilyLift.Local.blockFamilyFiniteLift q c D g) := by
  apply Finite.Sl.Local.finite_product_sl3_lift_commute q D
  intro g
  rw [BlockFamilyLift.Local.blockFamilyFiniteLift_projection]
  apply Commute.symm
  apply RepresentationTheory.Hecke.RadialDilation.FinitePadicCommutation.Realization.finitePadicSymplecticInclusion_commute
  rw [hm]
  exact Commute.one_right _

end Local

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

def nativeLocalDualBlocks : D.RationalSU →* (Fin s → RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) :=
  MonoidHom.pi fun τ => (Contragredient.Local.contragredient ℚ_[q]).comp
    ((Matrix.SpecialLinearGroup.map (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (τ, false))).comp
      (Geometry.ComplexBall.ArithmeticQuotientEquationsData.unitarySubgroup (NumberField.IsCMField.complexConj E).toRingHom
        D.pel.reference.b).subtype)

def nativeConjugatedRationalSplitting : D.RationalSU →* MpF :=
  (MulAut.conj u).toMonoidHom.comp
    (RationalSplitting.nativeRationalFiniteSplitting E D.pel.reference hg.reference_admissible hμ v hv e he D.weil)

theorem nativeConjugatedRationalSplitting_projection
    (hu : FiniteDilation.NativeFiniteCoordinateIdentity E D e u) (g : D.RationalSU) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom
      (D.weil.finite.project (nativeConjugatedRationalSplitting E D hg hμ v hv e he u g)) =
        BlockFamilyMatrices.Local.blockFamilySymplectic c (LocalSymplectic.nativeLocalUnitaryBlocks E D g) := by
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp _ (D.weil.finite.project (u *
    RationalSplitting.nativeRationalFiniteSplitting E D.pel.reference hg.reference_admissible hμ v hv e he D.weil g * u⁻¹)) = _
  have hp : D.weil.finite.project
      (RationalSplitting.nativeRationalFiniteSplitting E D.pel.reference hg.reference_admissible hμ v hv e he D.weil g) =
    D.weil.finite.project (D.weil.finiteLift
      (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E D.pel.reference e v he g)) := by
    rw [RationalSplitting.nativeRationalFiniteSplitting_covers, D.weil.finiteLift_covers]
  rw [D.weil.finite.project.map_mul, D.weil.finite.project.map_mul, hp,
    ← D.weil.finite.project.map_mul, ← D.weil.finite.project.map_mul]
  exact LocalSymplectic.native_local_symplectic_conjugation E D e v he c u hu g

theorem nativeRationalResidual_projection (hu : FiniteDilation.NativeFiniteCoordinateIdentity E D e u)
    (g : D.RationalSU) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom (D.weil.finite.project
      (nativeConjugatedRationalSplitting E D hg hμ v hv e he u g *
        (BlockFamilyLift.Local.blockFamilyFiniteLift q c D.weil (nativeLocalDualBlocks E D g))⁻¹)) = 1 := by
  rw [map_mul, map_inv, map_mul, map_inv,
    nativeConjugatedRationalSplitting_projection E D hg hμ v hv e he c u hu]
  change BlockFamilyMatrices.Local.blockFamilySymplectic c (LocalSymplectic.nativeLocalUnitaryBlocks E D g) *
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom (D.weil.finite.project
      (BlockFamilyLift.Local.blockFamilyFiniteLift q c D.weil (fun τ => Contragredient.Local.contragredient ℚ_[q]
        (LocalSymplectic.nativeLocalUnitaryBlocks E D g τ)))))⁻¹ = 1
  rw [BlockFamilyLift.Local.blockFamilyFiniteLift_dual_projection, mul_inv_cancel]

def nativeRationalAwayResidual (hu : FiniteDilation.NativeFiniteCoordinateIdentity E D e u) : D.RationalSU →* MpF :=
  Finite.Sl.Local.commutingResidualHom (nativeConjugatedRationalSplitting E D hg hμ v hv e he u)
    ((BlockFamilyLift.Local.blockFamilyFiniteLift q c D.weil).comp (nativeLocalDualBlocks E D))
    (fun g h => Local.blockFamilyFiniteLift_commute_of_trivial_projection q c D.weil _
      (nativeRationalResidual_projection E D hg hμ v hv e he c u hu g) (nativeLocalDualBlocks E D h))

theorem nativeRationalAwayResidual_factorization (hu : FiniteDilation.NativeFiniteCoordinateIdentity E D e u)
    (g : D.RationalSU) :
    nativeRationalAwayResidual E D hg hμ v hv e he c u hu g *
      BlockFamilyLift.Local.blockFamilyFiniteLift q c D.weil (nativeLocalDualBlocks E D g) =
        nativeConjugatedRationalSplitting E D hg hμ v hv e he u g :=
  inv_mul_cancel_right _ _

theorem nativeRationalAwayResidual_commute (hu : FiniteDilation.NativeFiniteCoordinateIdentity E D e u)
    (g : D.RationalSU) :
    ∀ a, Commute (nativeRationalAwayResidual E D hg hμ v hv e he c u hu g)
      (BlockFamilyLift.Local.blockFamilyFiniteLift q c D.weil a) :=
  Local.blockFamilyFiniteLift_commute_of_trivial_projection q c D.weil _
    (nativeRationalResidual_projection E D hg hμ v hv e he c u hu g)

theorem nativeRationalAwayResidual_other_prime (hu : FiniteDilation.NativeFiniteCoordinateIdentity E D e u)
    (g : D.RationalSU) (p : ℕ) [Fact p.Prime] (hpq : p ≠ q) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).toRingHom
      (D.weil.finite.project (nativeRationalAwayResidual E D hg hμ v hv e he c u hu g)) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[p]) (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E D.pel.reference e v he g) := by
  obtain ⟨S, hS, _⟩ := hu
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp _ (D.weil.finite.project ((u *
    RationalSplitting.nativeRationalFiniteSplitting E D.pel.reference hg.reference_admissible hμ v hv e he D.weil g * u⁻¹) *
      (BlockFamilyLift.Local.blockFamilyFiniteLift q c D.weil (nativeLocalDualBlocks E D g))⁻¹)) = _
  simp only [map_mul, map_inv]
  rw [hS, BlockFamilyLift.Local.blockFamilyFiniteLift_projection, RationalSplitting.nativeRationalFiniteSplitting_covers]
  simp only [RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic, MonoidHom.comp_apply,
    RepresentationTheory.Hecke.RadialDilation.FinitePadicOtherPrime.Realization.finitePadicSymplecticInclusion_other_prime q p hpq,
    RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.rationalSymplectic_finite_projection, inv_one, one_mul, mul_one]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalResidual
