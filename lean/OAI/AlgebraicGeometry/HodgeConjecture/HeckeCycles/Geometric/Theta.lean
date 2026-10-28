import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.Action

/-! # Theta -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.Theta.CM

noncomputable section

section

/-! The complete implemented GeometricTheta specification is an explicit named
prerequisite. Its theorem stub is never used; the separate type audit
compares every hypothesis and conclusion with the committed statement. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
open OAI.RepresentationTheory.Theta.Geometric.Intrinsic.Action

def GeometricThetaInput : Prop := ∀
    {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (_hs : 0 < s) (_hdegree : Module.finrank ℚ E = 2 * s)
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [IsTopologicalGroup Ga]
    [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hgeometry : D.pel.HasIntegralModelGeometry)
    (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)
    (_hC47 : RepresentationTheory.Theta.Geometric.TateComparison.TateComparisonOutput D.pel hgeometry hgood hIsogenyQuotient)
    (_hcoordinates : D.HasFiniteCoordinates)
    (_hholomorphic : D.HasHolomorphicThetaData)
    (_hautomorphy : D.HasRationalThetaCovariance)
    (_hE47 : DenseRange D.rationalFinite),
    ∃ A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel,
      A.IsRealization D.pel hgeometry hgood hIsogenyQuotient ∧
    ∃ (e : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ]
        RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
      (eComplex : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℂ]
        ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished),
      eComplex = RepresentationTheory.Theta.Geometric.Complexify.complexifyHeckeEquiv e ∧

      -- Characteristic double-coset operators retain their raw normalization.
      (∀ a : RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.ActiveWeight, ∃ T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q,
        AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.activeSLRepresentative q a) T ∧
        RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished e T =
          A.basis (RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.activeType D.pel.reference.distinguished a)) ∧

    ∃ (j : Fin D.pel.componentCount) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
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
        D.activeFormsComplex rhoForms e h (Θ φ) = Θ (D.sphericalWeilComplex h φ))

end

/-! The entire GeometricTheta conclusion, retaining its chosen action, raw operators,
actual branches, projectors, unique canonical lift and covariance. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
open OAI.RepresentationTheory.Theta.Geometric.Intrinsic.Action

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [IsTopologicalGroup Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
  (hgeometry : D.pel.HasIntegralModelGeometry) (hgood : D.pel.IsGoodCompletelySplitPrime)
  (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)

def Output : Prop :=
    ∃ A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel,
      A.IsRealization D.pel hgeometry hgood hIsogenyQuotient ∧
    ∃ (e : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ]
        RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
      (eComplex : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℂ]
        ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished),
      eComplex = RepresentationTheory.Theta.Geometric.Complexify.complexifyHeckeEquiv e ∧

      -- Characteristic double-coset operators retain their raw normalization.
      (∀ a : RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.ActiveWeight, ∃ T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q,
        AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.activeSLRepresentative q a) T ∧
        RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished e T =
          A.basis (RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.activeType D.pel.reference.distinguished a)) ∧

    ∃ (j : Fin D.pel.componentCount) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
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
        D.activeFormsComplex rhoForms e h (Θ φ) = Θ (D.sphericalWeilComplex h φ))

theorem from_input (hGeometricTheta : GeometricThetaInput)
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hTateComparison : RepresentationTheory.Theta.Geometric.TateComparison.TateComparisonOutput D.pel hgeometry hgood hIsogenyQuotient)
    (hcoordinates : D.HasFiniteCoordinates) (hholomorphic : D.HasHolomorphicThetaData)
    (hcovariance : D.HasRationalThetaCovariance) (hdense : DenseRange D.rationalFinite) :
    Output D hgeometry hgood hIsogenyQuotient :=
  hGeometricTheta hs hdegree D hgeometry hgood hIsogenyQuotient hTateComparison hcoordinates hholomorphic hcovariance hdense

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.Theta.CM
