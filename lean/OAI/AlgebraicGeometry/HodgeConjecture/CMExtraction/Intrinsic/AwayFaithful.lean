import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayTopology
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalUnitaryFaithful

/-! # Away Faithful -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayFaithful

noncomputable section

section

/-! The actual away projection retains every rational matrix at primes
other than q. It is therefore faithful on the native rational residual
range, so the natural induced away topology is Hausdorff. -/

open scoped Classical _root_.Matrix

section Local
variable (q : ℕ) [Fact q.Prime] {Place : Type} [Fintype Place] [DecidableEq Place]
  {n : ℕ} (c : (Place × Fin 3) ≃ Fin n) (μ : Place)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA) (u : MpF) (S : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ_[q])
  (hu : D.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q S)

include hu in
theorem coordinateDualLift_other_prime (p : ℕ) [Fact p.Prime] (hpq : p ≠ q) (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).toRingHom (D.finite.project (CoordinateDualHecke.Local.coordinateDualLift q c μ D u g)) = 1 := by
  rw [CoordinateDualHecke.Local.coordinateDualLift_projection, hu]
  simp only [map_mul, map_inv, RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic, MonoidHom.comp_apply,
    RepresentationTheory.Hecke.RadialDilation.FinitePadicOtherPrime.Realization.finitePadicSymplecticInclusion_other_prime q p hpq, inv_one, one_mul]

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
  (hu : FiniteDilation.NativeFiniteCoordinateIdentity E D e u)

theorem activeResidual_other_prime (g : D.RationalSU) (p : ℕ) [Fact p.Prime] (hpq : p ≠ q) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).toRingHom
      (D.weil.finite.project (RepresentationTheory.Hecke.BlockResidual.SphericalActionIntrinsic.activeResidual E D hg hμ v hv e he c u hu g)) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[p]) (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E D.pel.reference e v he g) := by
  have hu' := hu
  obtain ⟨S, hS, _⟩ := hu'
  have hf := RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeSplitting_rational E D hg hμ v hv e he c u hu g
  change CoordinateDualHecke.Local.coordinateDualLift q c D.pel.reference.distinguished D.weil u
      (LocalSymplectic.nativeLocalUnitaryBlocks E D g D.pel.reference.distinguished) *
      RepresentationTheory.Hecke.BlockResidual.SphericalActionIntrinsic.activeResidual E D hg hμ v hv e he c u hu g = _ at hf
  have h := congrArg (fun m : MpF => RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).toRingHom (D.weil.finite.project m)) hf
  simp only [map_mul] at h
  rw [coordinateDualLift_other_prime q c D.pel.reference.distinguished D.weil u S hS p hpq,
    one_mul, RationalSplitting.nativeRationalFiniteSplitting_covers, RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.rationalSymplectic_finite_projection] at h
  exact h

end

/-! The natural away matrix topology is Hausdorff: a single prime outside
q already distinguishes every element of the rational residual range. -/

open scoped Classical _root_.Matrix

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

theorem projectedActiveResidual_injective :
    Function.Injective (D.weil.finite.project.comp (RepresentationTheory.Hecke.BlockResidual.SphericalActionIntrinsic.activeResidual E D hg hμ v hv e he c u hu)) := by
  obtain ⟨p, hpq, hp⟩ := Nat.exists_infinite_primes (q + 1)
  let : Fact p.Prime := ⟨hp⟩
  have hpq' : p ≠ q := by omega
  intro g h hgh
  have hm := congrArg (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).toRingHom) hgh
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).toRingHom
      (D.weil.finite.project (RepresentationTheory.Hecke.BlockResidual.SphericalActionIntrinsic.activeResidual E D hg hμ v hv e he c u hu g)) =
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).toRingHom
      (D.weil.finite.project (RepresentationTheory.Hecke.BlockResidual.SphericalActionIntrinsic.activeResidual E D hg hμ v hv e he c u hu h)) at hm
  rw [activeResidual_other_prime E D hg hμ v hv e he c u hu g p hpq',
    activeResidual_other_prime E D hg hμ v hv e he c u hu h p hpq'] at hm
  exact RationalUnitaryFaithful.Intrinsic.nativeRationalSymplectic_local_injective E D.pel.reference e v he (algebraMap ℚ ℚ_[p]) hm

theorem nativeAwayMatrixHom_injective :
    Function.Injective (AwayTopology.nativeAwayMatrixHom E D hg hμ v hv e he c u hu) := by
  intro a b hab
  obtain ⟨g, hg'⟩ := a.property
  obtain ⟨h, hh'⟩ := b.property
  have hm : D.weil.finite.project a.val = D.weil.finite.project b.val := by
    apply Subtype.ext
    exact congrArg Units.val hab
  have hgh : g = h := projectedActiveResidual_injective E D hg hμ v hv e he c u hu
    (show D.weil.finite.project (RepresentationTheory.Hecke.BlockResidual.SphericalActionIntrinsic.activeResidual E D hg hμ v hv e he c u hu g) =
      D.weil.finite.project (RepresentationTheory.Hecke.BlockResidual.SphericalActionIntrinsic.activeResidual E D hg hμ v hv e he c u hu h) by rw [hg', hh', hm])
  apply Subtype.ext
  exact hg'.symm.trans ((congrArg (RepresentationTheory.Hecke.BlockResidual.SphericalActionIntrinsic.activeResidual E D hg hμ v hv e he c u hu) hgh).trans hh')

theorem nativeAway_injective : Function.Injective (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeAway E D hg hμ v hv e he c u hu) := by
  intro g h hgh
  exact projectedActiveResidual_injective E D hg hμ v hv e he c u hu
    (congrArg (fun a : RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu => D.weil.finite.project a.val) hgh)

theorem nativeAway_hausdorff :
    @T2Space (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu)
      (AwayTopology.nativeAwayTopology E D hg hμ v hv e he c u hu) := by
  let := AwayTopology.nativeAwayTopology E D hg hμ v hv e he c u hu
  have h : Topology.IsEmbedding (AwayTopology.nativeAwayMatrixHom E D hg hμ v hv e he c u hu) :=
    ⟨⟨rfl⟩, nativeAwayMatrixHom_injective E D hg hμ v hv e he c u hu⟩
  exact h.t2Space

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayFaithful
