import OAI.RepresentationTheory.Hecke.BlockResidual
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CotangentCovariance
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FiniteDilation

/-! # Intrinsic Datum -/

namespace OAI.RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic

noncomputable section

section

/-! A native GeometricTheta datum with the constructed period, cotangent projection
and rational-compatible finite splitting. Its away group is the actual
range of the residual rational lift. Topology, level and approximation
conditions are the geometric hypotheses of GeometricTheta; no theta-map or local
operator identification is an input.
-/

open scoped Classical _root_.Matrix

attribute [local instance] AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hμ : D.pel.reference.μ = E.val.toRingHom)
  (v : AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativeTensorPairing E D.pel.reference v x y))
  {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (u : MpF)
  (hu : AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FiniteDilation.NativeFiniteCoordinateIdentity E D e u)

abbrev NativeAway := (BlockResidual.SphericalActionIntrinsic.activeResidual E D hg hμ v hv e he c u hu).range

def nativeAway : D.RationalSU →* NativeAway E D hg hμ v hv e he c u hu :=
  (BlockResidual.SphericalActionIntrinsic.activeResidual E D hg hμ v hv e he c u hu).rangeRestrict

theorem nativeAway_commute (a : NativeAway E D hg hμ v hv e he c u hu)
    (g : Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    Commute a.val (AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateDualHecke.Local.coordinateDualLift q c D.pel.reference.distinguished D.weil u g) := by
  obtain ⟨γ, hγ⟩ := a.property
  rw [← hγ]
  exact BlockResidual.SphericalActionIntrinsic.activeResidual_commute E D hg hμ v hv e he c u hu γ g

def nativeSplitting : Theta.Geometric.SphericalGU.Spherical.SL3 q × NativeAway E D hg hμ v hv e he c u hu →* MpF where
  toFun p := AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateDualHecke.Local.coordinateDualLift q c D.pel.reference.distinguished D.weil u p.1 * p.2.val
  map_one' := by simp
  map_mul' x y := by
    change AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateDualHecke.Local.coordinateDualLift q c D.pel.reference.distinguished D.weil u (x.1 * y.1) *
      (x.2.val * y.2.val) = _
    rw [map_mul]
    have hc := nativeAway_commute E D hg hμ v hv e he c u hu x.2 y.1
    calc
      _ = AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateDualHecke.Local.coordinateDualLift q c D.pel.reference.distinguished D.weil u x.1 *
          (AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateDualHecke.Local.coordinateDualLift q c D.pel.reference.distinguished D.weil u y.1 * x.2.val) * y.2.val := by group
      _ = AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateDualHecke.Local.coordinateDualLift q c D.pel.reference.distinguished D.weil u x.1 *
          (x.2.val * AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateDualHecke.Local.coordinateDualLift q c D.pel.reference.distinguished D.weil u y.1) * y.2.val := by rw [hc.eq]
      _ = _ := by group

theorem nativeSplitting_local (g : Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    nativeSplitting E D hg hμ v hv e he c u hu (g, 1) =
      AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateDualHecke.Local.coordinateDualLift q c D.pel.reference.distinguished D.weil u g := by
  simp [nativeSplitting]

theorem nativeSplitting_rational (g : D.RationalSU) :
    nativeSplitting E D hg hμ v hv e he c u hu
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LocalSymplectic.nativeLocalUnitaryBlocks E D g D.pel.reference.distinguished,
        nativeAway E D hg hμ v hv e he c u hu g) =
      AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalSplitting.nativeRationalFiniteSplitting E D.pel.reference hg.reference_admissible hμ v hv e he D.weil g := by
  change AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateDualHecke.Local.coordinateDualLift q c D.pel.reference.distinguished D.weil u
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LocalSymplectic.nativeLocalUnitaryBlocks E D g D.pel.reference.distinguished) *
        BlockResidual.SphericalActionIntrinsic.activeResidual E D hg hμ v hv e he c u hu g = _
  rw [← (BlockResidual.SphericalActionIntrinsic.activeResidual_commute E D hg hμ v hv e he c u hu g
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LocalSymplectic.nativeLocalUnitaryBlocks E D g D.pel.reference.distinguished)).eq]
  change (u⁻¹ * ((u * AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalSplitting.nativeRationalFiniteSplitting E D.pel.reference
      hg.reference_admissible hμ v hv e he D.weil g * u⁻¹) *
      (BlockResidual.SphericalActionIntrinsic.activeRationalLift E D c g)⁻¹) * (u⁻¹)⁻¹) *
    (u⁻¹ * BlockResidual.SphericalActionIntrinsic.activeRationalLift E D c g * (u⁻¹)⁻¹) = _
  group

variable [TopologicalSpace (NativeAway E D hg hμ v hv e he c u hu)]
  (L : OpenSubgroup (NativeAway E D hg hμ v hv e he c u hu))

def nativeDatum : Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3)
    (NativeAway E D hg hμ v hv e he c u hu) MpR MpF MpA where
  pel := D.pel
  localEmbedding := AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel
  away := nativeAway E D hg hμ v hv e he c u hu
  localLevel := D.localLevel
  awayLevel := L
  weil := D.weil
  splitting := nativeSplitting E D hg hμ v hv e he c u hu
  period := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaCoordinates.Multiplicity.nativeThetaPeriod E D.pel.reference hg.reference_admissible hμ v hv e he
  project := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CotangentTheta.Multiplicity.nativeCotangentProjection E D.pel.reference hg.reference_admissible hμ v hv e he

theorem nativeDatum_holomorphic :
    (nativeDatum E D hg hμ v hv e he c u hu L).HasHolomorphicThetaData := by
  exact AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CotangentCovariance.withNativeCotangentTheta_holomorphic E D hg hμ v hv e he

theorem nativeDatum_automorphy :
    (nativeDatum E D hg hμ v hv e he c u hu L).HasRationalThetaCovariance := by
  intro γ φ x
  change D.RationalSU at γ
  have hx : x.val ∈ D.pel.reference.domain := by
    rw [AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodDomain.Multiplicity.native_domain_eq_ball E D.pel.reference]
    exact x.property
  change (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CotangentTheta.Multiplicity.nativeCotangentThetaOneForm E D.pel.reference hg.reference_admissible hμ v hv e he
    (D.weil.finite.action
      (nativeSplitting E D hg hμ v hv e he c u hu
        (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LocalSymplectic.nativeLocalUnitaryBlocks E D γ D.pel.reference.distinguished,
          nativeAway E D hg hμ v hv e he c u hu γ)) φ)
    (Theta.Geometric.Period.Ne.rationalPeriodPerm D.pel.reference.b D.pel.reference.μ γ x.val)).comp
      (fderiv ℂ (Theta.Geometric.Period.Ne.rationalPeriodPerm D.pel.reference.b D.pel.reference.μ γ) x.val) = _
  rw [nativeSplitting_rational E D hg hμ v hv e he c u hu γ]
  exact AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CotangentCovariance.nativeCotangentTheta_covariance E D.pel.reference hg.reference_admissible
    hμ v hv e he D.weil γ φ ⟨x.val, hx⟩

end

open scoped Classical _root_.Matrix

attribute [local instance] AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hμ : D.pel.reference.μ = E.val.toRingHom)
  (v : AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativeTensorPairing E D.pel.reference v x y))
  {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (u : MpF)
  (hu : AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FiniteDilation.NativeFiniteCoordinateIdentity E D e u)
  [TopologicalSpace (NativeAway E D hg hμ v hv e he c u hu)]
  (L : OpenSubgroup (NativeAway E D hg hμ v hv e he c u hu))

theorem nativeDatum_finiteCoordinates (hc : D.HasFiniteCoordinates)
    (hL : ∀ γ : D.RationalSU,
      nativeAway E D hg hμ v hv e he c u hu γ ∈ L ↔
        γ ∈ D.rationalAwayLevel ∧ ∀ w : Fin s × Bool,
          w.1 ≠ D.pel.reference.distinguished →
            D.localMatrix w γ ∈ Theta.Geometric.SphericalGU.Spherical.integralSL3 q) :
    (nativeDatum E D hg hμ v hv e he c u hu L).HasFiniteCoordinates := by
  have hemb : AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel = D.localEmbedding :=
    funext fun i => (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FiniteDilation.activeLocalEmbedding_eq_native E D hc i).symm
  refine ⟨?_, ?_, ?_⟩
  · intro i a
    exact AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding_onIntegers D.pel i a
  · intro i
    simpa only [Theta.Geometric.Data.ActiveHeckeThetaData.localReferenceLattice, nativeDatum, hemb] using hc.2.1 i
  · intro γ
    change nativeAway E D hg hμ v hv e he c u hu γ ∈ L ↔
      γ ∈ D.rationalAwayLevel ∧ ∀ w : Fin s × Bool,
        w.1 ≠ D.pel.reference.distinguished →
          (Matrix.SpecialLinearGroup.map (AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel w)) γ.val ∈
            Theta.Geometric.SphericalGU.Spherical.integralSL3 q
    rw [hemb]
    exact hL γ

end

end OAI.RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic
