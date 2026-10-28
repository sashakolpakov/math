import OAI.RepresentationTheory.Hecke.ThetaCentral
import OAI.RepresentationTheory.Hecke.IntrinsicConclusion
import OAI.RepresentationTheory.Hecke.SphericalAction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate

/-! # Theta -/

namespace OAI.RepresentationTheory.Hecke.Theta.CentralConstraintIntrinsic

noncomputable section

section

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
def ActualRadialConclusion
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
      (ThetaCentral.ConstraintIntrinsic.actualBettiRadial D hg Θ J) M ω

theorem actualRadialConclusion_of_native
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
    (h : IntrinsicConclusion.SphericalActionIntrinsic.NativeRadialConclusion D u rho eH Θ) :
    ActualRadialConclusion D u hg A coeff rho eH Θ := by
  obtain ⟨φ, hφ, J, hJ, hJval, hnz, M, ω, hM, hω, hroots, ρ, hρ, hcov, hdil, hsat⟩ := h
  have hbetti := ThetaCentral.ConstraintIntrinsic.actualBettiRadial_satake D hg P hq hIsogenyQuotient A hA coeff rho hrho eH heH
    Θ J M hM ω hω hcov hdil
  exact ⟨φ, hφ, J, hJ, hJval, hnz, M, ω, hM, hω, hroots, ρ, hρ, hcov, hdil, hsat,
    hbetti, ThetaCentral.ConstraintIntrinsic.actualCentralConclusion_of_satake D.pel hg hq hIsogenyQuotient _ hfull _ M ω hbetti⟩

theorem actualRadialConclusion_to_native
    (hg : D.pel.HasIntegralModelGeometry) (A : Theta.Geometric.TateComparison.Action D.pel)
    (coeff : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s →₀ ℕ)
    (rho : Theta.Geometric.SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA)
    (eH : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (h : ActualRadialConclusion D u hg A coeff rho eH Θ) :
    IntrinsicConclusion.SphericalActionIntrinsic.NativeRadialConclusion D u rho eH Θ := by
  obtain ⟨φ, hφ, J, hJ, hJval, hnz, M, ω, hM, hω, hroots, ρ, hρ, hcov, hdil, hsat, _, _⟩ := h
  exact ⟨φ, hφ, J, hJ, hJval, hnz, M, ω, hM, hω, hroots, ρ, hρ, hcov, hdil, hsat⟩

end

/-!
The full native SphericalAction output, including every GeometricTheta clause, strengthened
by Betti Satake and central conclusions for the same theta witnesses.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [DecidableEq (Fin s)]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA) (u : MpF)

/-- Complete GeometricTheta and SphericalAction outputs, with the actual Betti integration. -/
def ActualGeometricThetaOutput (hgeometry : D.pel.HasIntegralModelGeometry)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) : Prop :=
    ∃ A : Theta.Geometric.TateComparison.Action D.pel,
      A.IsRealization D.pel hgeometry hgood hIsogenyQuotient ∧
    ∃ coeff : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s →₀ ℕ,
      AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.Conclusion D.pel hgeometry hgood hIsogenyQuotient
        (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) ∧
    ∃ (e : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ]
        Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
      (eComplex : ℂ ⊗[ℚ] Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℂ]
        ℂ ⊗[ℚ] Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished),
      eComplex = Theta.Geometric.Complexify.complexifyHeckeEquiv e ∧

      -- Characteristic double-coset operators retain their raw normalization.
      (∀ a : Theta.Geometric.Intrinsic.Hecke.ActiveWeight, ∃ T : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q,
        AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (Theta.Geometric.Intrinsic.Hecke.activeSLRepresentative q a) T ∧
        Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished e T =
          A.basis (Theta.Geometric.Intrinsic.Hecke.activeType D.pel.reference.distinguished a)) ∧

    ∃ (j : Fin D.pel.componentCount) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
      (component : X.toOver ≅ D.componentComplex j) (cover : D.domain → X.analyticSpace),
      X.complexDimension = 2 ∧ D.IsPeriodUniformization X cover ∧

      -- Each actual cleared branch has exactly one special-linear coset
      -- and a rational representative preserving the entire away marking.
      (∀ a : Theta.Geometric.Intrinsic.Hecke.ActiveWeight,
        ∃ β : D.ClearedBranch (D.totalPeriodMap j X component cover) a ≃ Theta.Geometric.Intrinsic.Hecke.activeCosets q a,
          ∀ b : D.ClearedBranch (D.totalPeriodMap j X component cover) a,
            ∃ g : D.RationalSU,
              (QuotientGroup.mk (D.activeLocal g)⁻¹ :
                Theta.Geometric.SphericalGU.Spherical.SL3 q ⧸ Theta.Geometric.SphericalGU.Spherical.integralSL3 q) = (β b).val ∧
              D.away g ∈ D.awayLevel ∧
              ∀ L : D.domain,
                D.clearedBranchTarget A.shift b L =
                  D.totalPeriodMap j X component cover
                    ⟨D.periodMap g L.val, D.periodMap_preserves g L.val L.property⟩) ∧

      -- Commutation with the actual component projector separates both summands.
      (∀ h : ℂ ⊗[ℚ] Theta.Geometric.SphericalGU.Spherical.SL3Hecke q,
        (D.activeH1Complex A e h).comp (D.ballH1ComplexProjector j) =
          (D.ballH1ComplexProjector j).comp (D.activeH1Complex A e h)) ∧

    ∃ rhoForms : Theta.Geometric.SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA,
      (∀ h, D.IsRationalFormsPullback (A.algebraAction h) (rhoForms h)) ∧
    ∃ Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA,
      D.IsCanonicalThetaLift hgeometry j (D.totalPeriodMap j X component cover) Θ ∧
      (∀ Ψ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA,
        D.IsCanonicalThetaLift hgeometry j (D.totalPeriodMap j X component cover) Ψ → Ψ = Θ) ∧

      -- This is covariance of the canonical descended theta forms, extended by zero.
      (∀ (h : ℂ ⊗[ℚ] Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (φ : D.sphericalInputs),
        D.activeFormsComplex rhoForms e h (Θ φ) = Θ (D.sphericalWeilComplex h φ)) ∧
      (∀ f : D.sphericalInputs, Θ f ≠ 0 → ActualRadialConclusion D u hgeometry A coeff rhoForms e Θ)

/-- Destructure SphericalAction once and complete that same action and theta map. -/
theorem actualGeometricThetaOutput_of_native
    (hg : D.pel.HasIntegralModelGeometry)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation D.pel.complexAlbanese.X.left D.pel.complexAlbanese.X.hom)
    (hq : D.pel.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)
    (hTateComparison : Theta.Geometric.TateComparison.TateComparisonOutput D.pel hg hq hIsogenyQuotient)
    (h : IntrinsicConclusion.SphericalActionIntrinsic.NativeGeometricThetaOutput D u hg hq hIsogenyQuotient) :
    ActualGeometricThetaOutput D u hg hq hIsogenyQuotient := by
  obtain ⟨A, hA, eH, eComplex, heComplex, hraw, j, X, component, cover,
    hdim, hcover, hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov, hrad⟩ := h
  obtain ⟨coeff, hfull⟩ := AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.native_action_full_conclusion
    D.pel hg hq hIsogenyQuotient hTateComparison A hA
  have heH := AlgebraicGeometry.HodgeConjecture.CMExtraction.CanonicalActiveEquiv.Local.activeHeckeEquiv_eq_of_raw_matching
    q D.pel.reference.distinguished A.basis hA.basis eH hraw
  refine ⟨A, hA, coeff, hfull, eH, eComplex, heComplex, hraw, j, X, component, cover,
    hdim, hcover, hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov, ?_⟩
  intro f hf
  exact actualRadialConclusion_of_native D u hg P hq hIsogenyQuotient A hA coeff hfull
    rhoForms hrho eH heH Θ (hrad f hf)

/-- All geometric, canonical-theta and original radial clauses are retained. -/
theorem actualGeometricThetaOutput_to_native
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (h : ActualGeometricThetaOutput D u hg hq hIsogenyQuotient) :
    IntrinsicConclusion.SphericalActionIntrinsic.NativeGeometricThetaOutput D u hg hq hIsogenyQuotient := by
  obtain ⟨A, hA, coeff, _, eH, eComplex, heComplex, hraw, j, X, component, cover,
    hdim, hcover, hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov, hrad⟩ := h
  refine ⟨A, hA, eH, eComplex, heComplex, hraw, j, X, component, cover,
    hdim, hcover, hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov, ?_⟩
  intro f hf
  exact actualRadialConclusion_to_native D u hg A coeff rhoForms eH Θ (hrad f hf)

end

end OAI.RepresentationTheory.Hecke.Theta.CentralConstraintIntrinsic
