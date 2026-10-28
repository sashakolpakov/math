import OAI.RepresentationTheory.Hecke.ThetaOccurrence
import OAI.RepresentationTheory.Hecke.Theta
import OAI.RepresentationTheory.Hecke.IntrinsicConclusion
import OAI.RepresentationTheory.Hecke.SphericalAction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate

/-! # Occurrence Radial -/

namespace OAI.RepresentationTheory.Hecke.OccurrenceRadial.CentralConstraintIntrinsic

noncomputable section

open scoped Classical TensorProduct
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [DecidableEq (Fin s)] [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (u : MpF)

/-- Every original radial witness and clause is retained. The appended
conclusions use the actual class map composed with precisely Θ and J. -/
def FaithfulRadialConclusion
    (hg : D.pel.HasIntegralModelGeometry) (A : Theta.Geometric.TateComparison.Action D.pel)
    (coeff : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s →₀ ℕ)
    (rhoForms : Theta.Geometric.SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA)
    (eH : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA) : Prop :=
  ∃ (φ : RadialDilation.TestSections.Realization.lcCompactSpace (RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished)), φ ≠ 0 ∧
  ∃ (J : SphericalActionModelInverse.Radial q →ₗ[ℂ] D.sphericalInputs),
    Function.Injective J ∧
    (∀ b, (J b).val = AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ b) ∧
    (∃ b, Θ (J b) ≠ 0) ∧
  ∃ (M : ℕ) (ω : ℂ), 0 < M ∧ RadialDilation.Cm.algebraicUnitCircle ω ∧
    (∀ e₀ : ℂ, e₀ ^ M = ω → RadialDilation.Cm.algebraicUnitCircle e₀) ∧
  ∃ ρ : SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] Module.End ℂ (Θ.comp J).range,
    (∀ h y, (ρ h y).val = D.activeFormsComplex rhoForms eH h y.val) ∧
    (∀ h b, Θ (J (SphericalActionModelInverse.radialAction q .inverseCoset h b)) =
      D.activeFormsComplex rhoForms eH h (Θ (J b))) ∧
    (∀ b, Θ (J ((AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity.dilationEquiv q ^ M) b)) = ω • Θ (J b)) ∧
    SphericalActionModelInverse.RadialSatakeConclusion q .inverseCoset (V := (Θ.comp J).range)
      ρ (Θ.comp J).rangeRestrict M ω ∧
    ThetaCentral.ConstraintIntrinsic.ActualBettiConclusion D.pel hg (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff)
      (ThetaCentral.ConstraintIntrinsic.actualBettiRadial D hg Θ J) M ω ∧
    Function.Bijective (ThetaCentral.ConstraintIntrinsic.formsImageToBetti D hg Θ J) ∧
    (∃ b, ThetaCentral.ConstraintIntrinsic.actualBettiRadial D hg Θ J b ≠ 0) ∧
    ThetaOccurrence.CentralConstraintIntrinsic.FormsCentralConclusion D hg A coeff Θ J ρ M ω

theorem faithfulRadialConclusion_of_actual
    (hg : D.pel.HasIntegralModelGeometry)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation D.pel.complexAlbanese.X.left D.pel.complexAlbanese.X.hom)
    (hq : D.pel.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)
    (A : Theta.Geometric.TateComparison.Action D.pel) (hA : A.IsRealization D.pel hg hq hIsogenyQuotient)
    (coeff : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s →₀ ℕ)
    (hfull : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.Conclusion D.pel hg hq hIsogenyQuotient (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff))
    (rho : Theta.Geometric.SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA)
    (hrho : ∀ h, D.IsRationalFormsPullback (A.algebraAction h) (rho h))
    (eH : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (heH : eH = Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.pel.reference.distinguished)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (j : Fin D.pel.componentCount) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ D.componentComplex j)
    (cover : D.domain → X.analyticSpace) (hcover : D.IsPeriodUniformization X cover)
    (hΘ : D.IsCanonicalThetaLift hg j (D.totalPeriodMap j X component cover) Θ)
    (huniq : ∀ Ψ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA,
      D.IsCanonicalThetaLift hg j (D.totalPeriodMap j X component cover) Ψ → Ψ = Θ)
    (h : Theta.CentralConstraintIntrinsic.ActualRadialConclusion D u hg A coeff rho eH Θ) :
    FaithfulRadialConclusion D u hg A coeff rho eH Θ := by
  obtain ⟨φ, hφ, J, hJ, hJval, hnz, M, ω, hM, hω, hroots, ρ, hρ, hcov, hdil, hsat, hbetti⟩ := h
  exact ⟨φ, hφ, J, hJ, hJval, hnz, M, ω, hM, hω, hroots, ρ, hρ, hcov, hdil, hsat, hbetti,
    ThetaNonvanishing.CentralConstraintIntrinsic.canonicalTheta_formsImageToBetti_bijective D hg Θ j X component cover hcover hΘ huniq J,
    ThetaNonvanishing.CentralConstraintIntrinsic.canonicalTheta_actualBettiRadial_nonzero D hg Θ j X component cover hcover hΘ huniq J hnz,
    ThetaOccurrence.CentralConstraintIntrinsic.canonicalTheta_central_from_forms D hg P hq hIsogenyQuotient A hA coeff rho hrho eH heH
      Θ j X component cover hcover hΘ huniq J ρ hρ hfull M ω hbetti.1⟩

theorem faithfulRadialConclusion_to_actual
    (hg : D.pel.HasIntegralModelGeometry) (A : Theta.Geometric.TateComparison.Action D.pel)
    (coeff : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s →₀ ℕ)
    (rho : Theta.Geometric.SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA)
    (eH : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (h : FaithfulRadialConclusion D u hg A coeff rho eH Θ) :
    Theta.CentralConstraintIntrinsic.ActualRadialConclusion D u hg A coeff rho eH Θ := by
  obtain ⟨φ, hφ, J, hJ, hJval, hnz, M, ω, hM, hω, hroots, ρ, hρ, hcov, hdil, hsat, hbetti, _⟩ := h
  exact ⟨φ, hφ, J, hJ, hJval, hnz, M, ω, hM, hω, hroots, ρ, hρ, hcov, hdil, hsat, hbetti⟩

end

end OAI.RepresentationTheory.Hecke.OccurrenceRadial.CentralConstraintIntrinsic
