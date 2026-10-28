import OAI.RepresentationTheory.Hecke.BlockResidual
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FilledPEL

/-! # Active Residual Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ActiveResidualProjection

noncomputable section

/-! The q-adic projection of the actual native away residual consists
of the inactive blocks, conjugated back by the retained coordinate lift. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

open OAI.RepresentationTheory.Hecke.BlockResidual.SphericalActionIntrinsic OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FilledPEL.ParameterChoices

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

theorem nativeActiveResidual_projection (S : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin s × Fin 3) (Padic q))
    (huS : D.weil.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q S) (γ : D.RationalSU) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom
      (D.weil.finite.project (RepresentationTheory.Hecke.BlockResidual.SphericalActionIntrinsic.activeResidual E D hg hμ v hv e he c u hu γ)) =
      S⁻¹ * BlockFamilyMatrices.Local.blockFamilySymplectic c (fun τ => FilledPEL.ParameterChoices.nativeFilledBlock E D.pel γ (τ, false)) * S := by
  have hres : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom
      (D.weil.finite.project (RationalResidual.nativeRationalAwayResidual E D hg hμ v hv e he c u hu γ)) = 1 :=
    RationalResidual.nativeRationalResidual_projection E D hg hμ v hv e he c u hu γ
  have hb : RepresentationTheory.Hecke.BlockResidual.SphericalActionIntrinsic.inactiveBlocks D.pel.reference.distinguished (RationalResidual.nativeLocalDualBlocks E D γ) =
      (fun τ => Contragredient.Local.contragredient (Padic q) (FilledPEL.ParameterChoices.nativeFilledBlock E D.pel γ (τ, false))) := by
    funext τ
    change (if τ = D.pel.reference.distinguished then 1 else
      Contragredient.Local.contragredient (Padic q) (LocalSymplectic.nativeLocalUnitaryBlocks E D γ τ)) = _
    by_cases hτ : τ = D.pel.reference.distinguished
    · simp only [FilledPEL.ParameterChoices.nativeFilledBlock, hτ, ite_true, map_one]
    · simp only [FilledPEL.ParameterChoices.nativeFilledBlock, hτ, ite_false]
      rfl
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom (D.weil.finite.project
    (u⁻¹ * (RationalResidual.nativeConjugatedRationalSplitting E D hg hμ v hv e he u γ *
      (RepresentationTheory.Hecke.BlockResidual.SphericalActionIntrinsic.activeRationalLift E D c γ)⁻¹) * (u⁻¹)⁻¹)) = _
  rw [RepresentationTheory.Hecke.BlockResidual.SphericalActionIntrinsic.active_residual_formula E D hg hμ v hv e he c u hu γ]
  simp only [map_mul, map_inv, inv_inv, huS, RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion_projection,
    hres, hb, BlockFamilyLift.Local.blockFamilyFiniteLift_dual_projection, one_mul]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ActiveResidualProjection
