import OAI.RepresentationTheory.Hecke.IntrinsicDatum
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SphericalCoordinates

/-! # Away Phase -/

namespace OAI.RepresentationTheory.Hecke.AwayPhase.SphericalActionIntrinsic

noncomputable section

/-! The constructed away residual fixes the active phase coordinates.
This is derived from its local block projection, before applying the
native spherical expansion theorem. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SphericalCoordinates.Local OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SphericalCoordinates

section Local
variable (q : ℕ) [Fact q.Prime] {Place : Type} [Fintype Place] [DecidableEq Place]
  {n : ℕ} (c : (Place × Fin 3) ≃ Fin n) (μ : Place)

theorem inactiveBlocks_phase (g : Place → Theta.Geometric.SphericalGU.Spherical.SL3 q)
    (w : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3) :
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic c (BlockResidual.SphericalActionIntrinsic.inactiveBlocks μ g)).val *ᵥ RadialDilation.FinitePhaseProjection.Realization.localBlockPhase q μ w =
      RadialDilation.FinitePhaseProjection.Realization.localBlockPhase q μ w := by
  funext i
  cases i with
  | inl p =>
    rw [AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic_inl]
    by_cases h : p.1 = μ
    · simp [RadialDilation.FinitePhaseProjection.Realization.localBlockPhase, BlockResidual.SphericalActionIntrinsic.inactiveBlocks, h]
    · simp only [RadialDilation.FinitePhaseProjection.Realization.localBlockPhase, Sum.elim_inl, ite_eq_right h]
      exact congrFun (Matrix.mulVec_zero _) p.2
  | inr p =>
    rw [AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic_inr]
    by_cases h : p.1 = μ
    · simp [RadialDilation.FinitePhaseProjection.Realization.localBlockPhase, BlockResidual.SphericalActionIntrinsic.inactiveBlocks, h]
    · simp only [RadialDilation.FinitePhaseProjection.Realization.localBlockPhase, Sum.elim_inr, ite_eq_right h]
      exact congrFun (Matrix.mulVec_zero _) p.2

end Local

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

theorem activeResidualConjugated_projection (g : D.RationalSU) :
    Theta.PoissonAutomorphyNormalizationData.mapSp (RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom
      (D.weil.finite.project (BlockResidual.SphericalActionIntrinsic.activeResidualConjugated E D hg hμ v hv e he c u hu g)) =
        AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic c
          (BlockResidual.SphericalActionIntrinsic.inactiveBlocks D.pel.reference.distinguished (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LocalSymplectic.nativeLocalUnitaryBlocks E D g)) := by
  change Theta.PoissonAutomorphyNormalizationData.mapSp _ (D.weil.finite.project
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalResidual.nativeConjugatedRationalSplitting E D hg hμ v hv e he u g *
      (BlockResidual.SphericalActionIntrinsic.activeRationalLift E D c g)⁻¹)) = _
  rw [BlockResidual.SphericalActionIntrinsic.active_residual_formula E D hg hμ v hv e he c u hu g, map_mul, map_mul]
  rw [show Theta.PoissonAutomorphyNormalizationData.mapSp (RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom
    (D.weil.finite.project (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalResidual.nativeRationalAwayResidual E D hg hμ v hv e he c u hu g)) = 1 from
      AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalResidual.nativeRationalResidual_projection E D hg hμ v hv e he c u hu g, one_mul]
  have hb : BlockResidual.SphericalActionIntrinsic.inactiveBlocks D.pel.reference.distinguished (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalResidual.nativeLocalDualBlocks E D g) =
      fun τ => AlgebraicGeometry.HodgeConjecture.CMExtraction.Contragredient.Local.contragredient ℚ_[q]
        (BlockResidual.SphericalActionIntrinsic.inactiveBlocks D.pel.reference.distinguished (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LocalSymplectic.nativeLocalUnitaryBlocks E D g) τ) := by
    funext τ
    change (if τ = D.pel.reference.distinguished then 1 else
      AlgebraicGeometry.HodgeConjecture.CMExtraction.Contragredient.Local.contragredient ℚ_[q] (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LocalSymplectic.nativeLocalUnitaryBlocks E D g τ)) =
      AlgebraicGeometry.HodgeConjecture.CMExtraction.Contragredient.Local.contragredient ℚ_[q] (if τ = D.pel.reference.distinguished then 1 else
        AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LocalSymplectic.nativeLocalUnitaryBlocks E D g τ)
    split_ifs <;> simp only [map_one]
  rw [hb, AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyLift.Local.blockFamilyFiniteLift_dual_projection]

theorem activeResidualConjugated_fixes_phase (g : D.RationalSU)
    (p t : Fin 3 → ℚ_[q]) :
    (D.weil.finite.project (BlockResidual.SphericalActionIntrinsic.activeResidualConjugated E D hg hμ v hv e he c u hu g)).val *ᵥ
      Sum.elim (RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished p)
        (RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished t) =
      Sum.elim (RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished p)
        (RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished t) := by
  change _ *ᵥ RadialDilation.FiniteBlockIntertwiner.Realization.finiteBlockPhase q D.pel.reference.distinguished (Sum.elim t p) =
    RadialDilation.FiniteBlockIntertwiner.Realization.finiteBlockPhase q D.pel.reference.distinguished (Sum.elim t p)
  apply RadialDilation.FinitePhaseProjection.Realization.finiteMatrix_localBlock_action q D.pel.reference.distinguished _ id
  intro w
  have hm := congrArg Subtype.val
    (activeResidualConjugated_projection E D hg hμ v hv e he c u hu g)
  change (D.weil.finite.project _).val.map (RadialDilation.FiniteSchur.Realization.finitePadicProjection q) = _ at hm
  rw [hm]
  exact inactiveBlocks_phase q c D.pel.reference.distinguished _ w

variable [TopologicalSpace (IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu)]
  (L : OpenSubgroup (IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu))

theorem nativeDatum_away_fixes_phase
    (g : IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu)
    (p t : Fin 3 → ℚ_[q]) :
    (D.weil.finite.project
      (u * (IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L).splitting (1, g) * u⁻¹)).val *ᵥ
      Sum.elim (RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished p)
        (RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished t) =
      Sum.elim (RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished p)
        (RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished t) := by
  obtain ⟨γ, hγ⟩ := g.property
  have hm : u * (IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L).splitting (1, g) * u⁻¹ =
      BlockResidual.SphericalActionIntrinsic.activeResidualConjugated E D hg hμ v hv e he c u hu γ := by
    change u * (AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateDualHecke.Local.coordinateDualLift q c D.pel.reference.distinguished D.weil u 1 * g.val) * u⁻¹ = _
    rw [map_one, one_mul, ← hγ]
    change u * (u⁻¹ * _ * (u⁻¹)⁻¹) * u⁻¹ = _
    group
  rw [hm]
  exact activeResidualConjugated_fixes_phase E D hg hμ v hv e he c u hu γ p t

end

end OAI.RepresentationTheory.Hecke.AwayPhase.SphericalActionIntrinsic
