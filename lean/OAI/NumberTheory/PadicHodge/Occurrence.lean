import OAI.NumberTheory.PadicHodge.OccurrenceRadial
import OAI.NumberTheory.PadicHodge.Theta
import OAI.RepresentationTheory.Hecke.Occurrence

/-! # Occurrence -/

namespace OAI.NumberTheory.PadicHodge.Occurrence.FrobeniusSlope

noncomputable section

/-! Strengthen exactly the existing FullOutput witnesses with faithful
forms-to-Betti occurrence and its retained-root Frobenius application. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type}
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type}
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA) (u : MpF)

open OAI.RepresentationTheory.Hecke.Occurrence.CentralConstraintIntrinsic
open OAI.NumberTheory.PadicHodge.OccurrenceRadial.FrobeniusSlope
variable (ιE : E →ₐ[ℚ] AlgebraicClosure ℚ) (v : AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Odd.Sign E)

def FaithfulOutput (hgeometry : D.pel.HasIntegralModelGeometry)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) : Prop :=
    ∃ A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel,
      A.IsRealization D.pel hgeometry hgood hIsogenyQuotient ∧
    ∃ coeff : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s →₀ ℕ,
    ∃ hfull : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.Conclusion D.pel hgeometry hgood hIsogenyQuotient
        (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff),
    ∃ (e : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ]
        RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
      (eComplex : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℂ]
        ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished),
      eComplex = RepresentationTheory.Theta.Geometric.Complexify.complexifyHeckeEquiv e ∧

      -- Characteristic double-coset operators retain their raw normalization.
      (∀ a : RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.ActiveWeight, ∃ T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q,
        AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.activeSLRepresentative q a) T ∧
        RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished e T =
          A.basis (RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.activeType D.pel.reference.distinguished a)) ∧

    ∃ (j : Fin D.pel.componentCount) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
      (component : X.toOver ≅ D.componentComplex j) (cover : D.domain → X.analyticSpace),
      X.complexDimension = 2 ∧ D.IsPeriodUniformization X cover ∧

      -- Each actual cleared branch has exactly one special-linear coset
      -- and a rational representative preserving the entire away marking.
      (∀ a : RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.ActiveWeight,
        ∃ β : D.ClearedBranch (D.totalPeriodMap j X component cover) a ≃ RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.activeCosets q a,
          ∀ b : D.ClearedBranch (D.totalPeriodMap j X component cover) a,
            ∃ g : D.RationalSU,
              (QuotientGroup.mk (D.activeLocal g)⁻¹ :
                RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q ⧸ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) = (β b).val ∧
              D.away g ∈ D.awayLevel ∧
              ∀ L : D.domain,
                D.clearedBranchTarget A.shift b L =
                  D.totalPeriodMap j X component cover
                    ⟨D.periodMap g L.val, D.periodMap_preserves g L.val L.property⟩) ∧

      -- Commutation with the actual component projector separates both summands.
      (∀ h : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q,
        (D.activeH1Complex A e h).comp (D.ballH1ComplexProjector j) =
          (D.ballH1ComplexProjector j).comp (D.activeH1Complex A e h)) ∧

    ∃ rhoForms : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA,
      (∀ h, D.IsRationalFormsPullback (A.algebraAction h) (rhoForms h)) ∧
    ∃ Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA,
      D.IsCanonicalThetaLift hgeometry j (D.totalPeriodMap j X component cover) Θ ∧
      (∀ Ψ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA,
        D.IsCanonicalThetaLift hgeometry j (D.totalPeriodMap j X component cover) Ψ → Ψ = Θ) ∧

      -- This is covariance of the canonical descended theta forms, extended by zero.
      (∀ (h : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (φ : D.sphericalInputs),
        D.activeFormsComplex rhoForms e h (Θ φ) = Θ (D.sphericalWeilComplex h φ)) ∧
      (∀ f : D.sphericalInputs, Θ f ≠ 0 → OccurrenceRadial.FrobeniusSlope.FaithfulRadial E D u ιE v hgeometry hgood hIsogenyQuotient A coeff hfull rhoForms e Θ)

/-- The full GeometricTheta and FrobeniusSlope output is destructured once. -/
theorem faithfulOutput_of_original
    (hg : D.pel.HasIntegralModelGeometry)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation D.pel.complexAlbanese.X.left D.pel.complexAlbanese.X.hom)
    (hq : D.pel.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)
    (h : Theta.FrobeniusSlope.FullOutput E D u ιE v hg hq hIsogenyQuotient) :
    FaithfulOutput E D u ιE v hg hq hIsogenyQuotient := by
  obtain ⟨A, hA, coeff, hfull, eH, eComplex, heComplex, hraw, j, X, component, cover,
    hdim, hcover, hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov, hrad⟩ := h
  have heH := AlgebraicGeometry.HodgeConjecture.CMExtraction.CanonicalActiveEquiv.Local.activeHeckeEquiv_eq_of_raw_matching
    q D.pel.reference.distinguished A.basis hA.basis eH hraw
  refine ⟨A, hA, coeff, hfull, eH, eComplex, heComplex, hraw, j, X, component, cover,
    hdim, hcover, hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov, ?_⟩
  intro f hf
  exact OccurrenceRadial.FrobeniusSlope.faithfulRadial_of_original E D u ιE v hg hq hIsogenyQuotient A coeff hfull rhoForms eH Θ
    P hA hrho heH j X component cover hcover hΘ huniq (hrad f hf)

theorem faithfulOutput_to_original
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (h : FaithfulOutput E D u ιE v hg hq hIsogenyQuotient) :
    Theta.FrobeniusSlope.FullOutput E D u ιE v hg hq hIsogenyQuotient := by
  obtain ⟨A, hA, coeff, hfull, eH, eComplex, heComplex, hraw, j, X, component, cover,
    hdim, hcover, hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov, hrad⟩ := h
  refine ⟨A, hA, coeff, hfull, eH, eComplex, heComplex, hraw, j, X, component, cover,
    hdim, hcover, hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov, ?_⟩
  intro f hf
  exact OccurrenceRadial.FrobeniusSlope.faithfulRadial_to_original E D u ιE v hg hq hIsogenyQuotient A coeff hfull rhoForms eH Θ (hrad f hf)

theorem faithfulOutput_to_CentralConstraint
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (h : FaithfulOutput E D u ιE v hg hq hIsogenyQuotient) :
    RepresentationTheory.Hecke.Occurrence.CentralConstraintIntrinsic.FaithfulGeometricThetaOutput D u hg hq hIsogenyQuotient := by
  obtain ⟨A, hA, coeff, hfull, eH, eComplex, heComplex, hraw, j, X, component, cover,
    hdim, hcover, hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov, hrad⟩ := h
  refine ⟨A, hA, coeff, hfull, eH, eComplex, heComplex, hraw, j, X, component, cover,
    hdim, hcover, hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov, ?_⟩
  intro f hf
  exact OccurrenceRadial.FrobeniusSlope.faithfulRadial_to_CentralConstraint E D u ιE v hg hq hIsogenyQuotient A coeff hfull rhoForms eH Θ (hrad f hf)

end

end OAI.NumberTheory.PadicHodge.Occurrence.FrobeniusSlope
