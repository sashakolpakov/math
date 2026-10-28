import OAI.RepresentationTheory.Hecke.GeometricFamily
import OAI.RepresentationTheory.Hecke.IntrinsicConclusion

/-! # Geometric -/

namespace OAI.RepresentationTheory.Hecke.Geometric.GaloisValuation

noncomputable section

/-! Every clause of the complete native GeometricTheta output is retained.
The radial conclusion additionally carries its original scalar-product
witness and the full signed Galois valuation rule. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

section GenericOutput
variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type}
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)

/-- Complete GeometricTheta output with a predicate on the very same canonical theta map. -/
def WithRadialProperty
    (P : (Theta.Geometric.SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA) →
      (Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished) →
      (D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA) → Prop)
    (hgeometry : D.pel.HasIntegralModelGeometry) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) : Prop :=
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
      (∀ f : D.sphericalInputs, Θ f ≠ 0 → P rhoForms e Θ)

end GenericOutput

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E]
  [NumberField.IsCMField E] {K : Type}
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type}
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA) (u : MpF)
  (ιE : E →ₐ[ℚ] IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar) (v : AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Odd.Sign E)

/-- The complete geometric output and fixed-witness signed parameters. -/
def GeometricGeometricThetaOutput (hg : D.pel.HasIntegralModelGeometry)
    (hq : D.pel.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) : Prop :=
  WithRadialProperty D (fun rhoForms eH Θ => GeometricFamily.GaloisValuation.RadialWithSigns E D u ιE v rhoForms eH Θ)
    hg hq hIsogenyQuotient

/-- Forget only the extra arithmetic data, retaining the entire SphericalAction native output. -/
theorem geometricGeometricThetaOutput_to_native
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)
    (h : GeometricGeometricThetaOutput E D u ιE v hg hq hIsogenyQuotient) :
    IntrinsicConclusion.SphericalActionIntrinsic.NativeGeometricThetaOutput D u hg hq hIsogenyQuotient := by
  obtain ⟨A, hA, eH, eComplex, heComplex, hraw, j, X, component, cover,
    hdim, hcover, hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov, hsign⟩ := h
  refine ⟨A, hA, eH, eComplex, heComplex, hraw, j, X, component, cover,
    hdim, hcover, hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov, ?_⟩
  intro f hf
  exact GeometricFamily.GaloisValuation.radialWithSigns_to_native E D u ιE v rhoForms eH Θ (hsign f hf)

end

end OAI.RepresentationTheory.Hecke.Geometric.GaloisValuation
