import OAI.RepresentationTheory.Theta.Geometric.Covariance
import OAI.RepresentationTheory.Theta.Geometric.CanonicalExistence
import OAI.RepresentationTheory.Theta.Geometric.Reference.Quotient

/-! # Theorem -/

namespace OAI.RepresentationTheory.Theta.Geometric.Theorem

noncomputable section

/-! The full repaired GeometricTheta conclusion from its original hypotheses and
accepted TateComparison output, including both summands and complex theta covariance. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

theorem active_hecke_action_and_finite_weil_covariance_constructed
    {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [IsTopologicalGroup Ga]
    [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hgeometry : D.pel.HasIntegralModelGeometry)
    (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)
    (hTateComparison : TateComparison.TateComparisonOutput D.pel hgeometry hgood hIsogenyQuotient)
    (hcoordinates : D.HasFiniteCoordinates)
    (hholomorphic : D.HasHolomorphicThetaData)
    (hautomorphy : D.HasRationalThetaCovariance)
    (hArithmetic : DenseRange D.rationalFinite) :
    ∃ A : TateComparison.Action D.pel,
      A.IsRealization D.pel hgeometry hgood hIsogenyQuotient ∧
    ∃ (e : SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ]
        SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
      (eComplex : ℂ ⊗[ℚ] SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℂ]
        ℂ ⊗[ℚ] SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished),
      eComplex = Complexify.complexifyHeckeEquiv e ∧

      -- Characteristic double-coset operators retain their raw normalization.
      (∀ a : Intrinsic.Hecke.ActiveWeight, ∃ T : SphericalGU.Spherical.SL3Hecke q,
        AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (SphericalGU.Spherical.integralSL3 q) (Intrinsic.Hecke.activeSLRepresentative q a) T ∧
        Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished e T =
          A.basis (Intrinsic.Hecke.activeType D.pel.reference.distinguished a)) ∧

    ∃ (j : Fin D.pel.componentCount) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
      (component : X.toOver ≅ D.componentComplex j) (cover : D.domain → X.analyticSpace),
      X.complexDimension = 2 ∧ D.IsPeriodUniformization X cover ∧

      -- Each actual cleared branch has exactly one special-linear coset
      -- and a rational representative preserving the entire away marking.
      (∀ a : Intrinsic.Hecke.ActiveWeight,
        ∃ β : D.ClearedBranch (D.totalPeriodMap j X component cover) a ≃ Intrinsic.Hecke.activeCosets q a,
          ∀ b : D.ClearedBranch (D.totalPeriodMap j X component cover) a,
            ∃ g : D.RationalSU,
              (QuotientGroup.mk (D.activeLocal g)⁻¹ :
                SphericalGU.Spherical.SL3 q ⧸ SphericalGU.Spherical.integralSL3 q) = (β b).val ∧
              D.away g ∈ D.awayLevel ∧
              ∀ L : D.domain,
                D.clearedBranchTarget A.shift b L =
                  D.totalPeriodMap j X component cover
                    ⟨D.periodMap g L.val, D.periodMap_preserves g L.val L.property⟩) ∧

      -- Commutation with the actual component projector separates both summands.
      (∀ h : ℂ ⊗[ℚ] SphericalGU.Spherical.SL3Hecke q,
        (D.activeH1Complex A e h).comp (D.ballH1ComplexProjector j) =
          (D.ballH1ComplexProjector j).comp (D.activeH1Complex A e h)) ∧

    ∃ rhoForms : SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA,
      (∀ h, D.IsRationalFormsPullback (A.algebraAction h) (rhoForms h)) ∧
    ∃ Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA,
      D.IsCanonicalThetaLift hgeometry j (D.totalPeriodMap j X component cover) Θ ∧
      (∀ Ψ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA,
        D.IsCanonicalThetaLift hgeometry j (D.totalPeriodMap j X component cover) Ψ → Ψ = Θ) ∧

      -- This is covariance of the canonical descended theta forms, extended by zero.
      (∀ (h : ℂ ⊗[ℚ] SphericalGU.Spherical.SL3Hecke q) (φ : D.sphericalInputs),
        D.activeFormsComplex rhoForms e h (Θ φ) = Θ (D.sphericalWeilComplex h φ))  := by
  obtain ⟨A, hA⟩ := TateComparison.TateComparisonOutput.produces_action D.pel hgeometry hgood hIsogenyQuotient hTateComparison
  let e := Active.Algebra.Spherical.activeHeckeEquiv q D.pel.reference.distinguished
  refine ⟨A, hA, e, Complexify.complexifyHeckeEquiv e, rfl, ?_⟩
  refine ⟨Active.Basis.Spherical.active_basis_matching q D.pel.reference.distinguished A.basis hA.basis, ?_⟩
  obtain ⟨j, X, component, cover, hdim, hcover, href⟩ :=
    D.exists_original_period_uniformization hgeometry hcoordinates hgood hs hdegree
  refine ⟨j, X, component, cover, hdim, hcover, ?_, ?_, ?_⟩
  · exact D.original_active_branch_bijection hgeometry hgood hIsogenyQuotient A hA hdegree hs hcoordinates hArithmetic
      j X component cover hcover href
  · exact D.original_active_H1_projector_commute hgeometry hgood hIsogenyQuotient A hA hdegree hs hcoordinates hArithmetic
      j X component cover hcover href
  · let Θ := D.thetaAlbaneseLift hgeometry j X component cover hcover hholomorphic hautomorphy
    have hΘ := D.thetaAlbaneseLift_isCanonical hgeometry j X component cover hcover hholomorphic hautomorphy
    refine ⟨D.heckeRationalForms hgeometry A, D.heckeRationalForms_spec hgeometry A, Θ, hΘ, ?_, ?_⟩
    · intro Ψ hΨ
      exact D.canonicalThetaLift_unique hgeometry j X component cover hcover Θ Ψ hΘ hΨ
    · exact D.original_complex_theta_covariance hgeometry hgood hIsogenyQuotient A hA hdegree hs hcoordinates hArithmetic
        j X component cover hcover href hholomorphic hautomorphy

end

end OAI.RepresentationTheory.Theta.Geometric.Theorem
