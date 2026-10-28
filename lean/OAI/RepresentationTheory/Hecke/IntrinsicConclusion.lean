import OAI.RepresentationTheory.Hecke.SphericalActionModelInverse
import OAI.RepresentationTheory.Hecke.SphericalAction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate

/-! # Intrinsic Conclusion -/

namespace OAI.RepresentationTheory.Hecke.IntrinsicConclusion.SphericalActionIntrinsic

noncomputable section

section

open scoped Classical TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [DecidableEq (Fin s)] [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (u : MpF)

/-- The representation is the actual forms action restricted to the image
of the same algebraic theta map on a constructed radial family. -/
def NativeRadialConclusion
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
      ρ (Θ.comp J).rangeRestrict M ω

end

/-!
The full output of GeometricTheta, strengthened by the native radial
conclusion for the same canonical theta map and the same forms action.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [DecidableEq (Fin s)]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA) (u : MpF)

/-- GeometricTheta's complete conclusion plus its native radial specialization. -/
def NativeGeometricThetaOutput (hgeometry : D.pel.HasIntegralModelGeometry)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) : Prop :=
    ∃ A : Theta.Geometric.TateComparison.Action D.pel,
      A.IsRealization D.pel hgeometry hgood hIsogenyQuotient ∧
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
      (∀ f : D.sphericalInputs, Θ f ≠ 0 → NativeRadialConclusion D u rhoForms e Θ)

/-- The strengthened result retains every clause of the full GeometricTheta output. -/
theorem nativeGeometricThetaOutput_to_full_GeometricThetaOutput
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (h : NativeGeometricThetaOutput D u hg hq hIsogenyQuotient) :
    AlgebraicGeometry.HodgeConjecture.CMExtraction.GeometricTheta.Intrinsic.GeometricThetaOutput D hg hq hIsogenyQuotient := by
  obtain ⟨A, hA, eH, eComplex, heComplex, hraw, j, X, component, cover,
    hdim, hcover, hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov, _⟩ := h
  exact ⟨A, hA, eH, eComplex, heComplex, hraw, j, X, component, cover,
    hdim, hcover, hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov⟩

end

end OAI.RepresentationTheory.Hecke.IntrinsicConclusion.SphericalActionIntrinsic
