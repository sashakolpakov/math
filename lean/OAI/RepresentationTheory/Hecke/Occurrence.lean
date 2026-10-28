import OAI.RepresentationTheory.Hecke.OccurrenceRadial
import OAI.RepresentationTheory.Hecke.Theta

/-! # Occurrence -/

namespace OAI.RepresentationTheory.Hecke.Occurrence.CentralConstraintIntrinsic

noncomputable section

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
def FaithfulGeometricThetaOutput (hgeometry : D.pel.HasIntegralModelGeometry)
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
      (∀ f : D.sphericalInputs, Θ f ≠ 0 → OccurrenceRadial.CentralConstraintIntrinsic.FaithfulRadialConclusion D u hgeometry A coeff rhoForms e Θ)

/-- Enrich the same witnesses; do not reselect the action, lift or radial family. -/
theorem faithfulGeometricThetaOutput_of_actual
    (hg : D.pel.HasIntegralModelGeometry)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation D.pel.complexAlbanese.X.left D.pel.complexAlbanese.X.hom)
    (hq : D.pel.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)
    (h : Theta.CentralConstraintIntrinsic.ActualGeometricThetaOutput D u hg hq hIsogenyQuotient) :
    FaithfulGeometricThetaOutput D u hg hq hIsogenyQuotient := by
  obtain ⟨A, hA, coeff, hfull, eH, eComplex, heComplex, hraw, j, X, component, cover,
    hdim, hcover, hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov, hrad⟩ := h
  have heH := AlgebraicGeometry.HodgeConjecture.CMExtraction.CanonicalActiveEquiv.Local.activeHeckeEquiv_eq_of_raw_matching
    q D.pel.reference.distinguished A.basis hA.basis eH hraw
  refine ⟨A, hA, coeff, hfull, eH, eComplex, heComplex, hraw, j, X, component, cover,
    hdim, hcover, hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov, ?_⟩
  intro f hf
  exact OccurrenceRadial.CentralConstraintIntrinsic.faithfulRadialConclusion_of_actual D u hg P hq hIsogenyQuotient A hA coeff hfull
    rhoForms hrho eH heH Θ j X component cover hcover hΘ huniq (hrad f hf)

/-- Every previously accepted actual-theta clause is preserved. -/
theorem faithfulGeometricThetaOutput_to_actual
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (h : FaithfulGeometricThetaOutput D u hg hq hIsogenyQuotient) :
    Theta.CentralConstraintIntrinsic.ActualGeometricThetaOutput D u hg hq hIsogenyQuotient := by
  obtain ⟨A, hA, coeff, hfull, eH, eComplex, heComplex, hraw, j, X, component, cover,
    hdim, hcover, hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov, hrad⟩ := h
  refine ⟨A, hA, coeff, hfull, eH, eComplex, heComplex, hraw, j, X, component, cover,
    hdim, hcover, hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov, ?_⟩
  intro f hf
  exact OccurrenceRadial.CentralConstraintIntrinsic.faithfulRadialConclusion_to_actual D u hg A coeff rhoForms eH Θ (hrad f hf)

end

end OAI.RepresentationTheory.Hecke.Occurrence.CentralConstraintIntrinsic
