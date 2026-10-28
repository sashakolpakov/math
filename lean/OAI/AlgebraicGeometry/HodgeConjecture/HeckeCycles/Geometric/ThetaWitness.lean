import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.Theta

/-! # Theta Witness -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaWitness.CM

noncomputable section

/-! Named access to every clause of the full GeometricTheta output. This packages
the actual chosen action, branches and canonical theta lift together. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
  (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)

structure Witness where
  action : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel
  realization : action.IsRealization D.pel hg hq hIsogenyQuotient
  active : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ]
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished
  activeComplex : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℂ]
    ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished
  complexification : activeComplex = RepresentationTheory.Theta.Geometric.Complexify.complexifyHeckeEquiv active
  raw : ∀ a : RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.ActiveWeight, ∃ T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q,
    AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.activeSLRepresentative q a) T ∧
      RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished active T =
        action.basis (RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.activeType D.pel.reference.distinguished a)
  index : Fin D.pel.componentCount
  variety : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety
  component : variety.toOver ≅ D.componentComplex index
  cover : D.domain → variety.analyticSpace
  dimension : variety.complexDimension = 2
  uniformization : D.IsPeriodUniformization variety cover
  branches : ∀ a : RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.ActiveWeight,
    ∃ β : D.ClearedBranch (D.totalPeriodMap index variety component cover) a ≃ RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.activeCosets q a,
      ∀ b : D.ClearedBranch (D.totalPeriodMap index variety component cover) a,
        ∃ g : D.RationalSU,
          (QuotientGroup.mk (D.activeLocal g)⁻¹ :
            RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q ⧸ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) = (β b).val ∧
          D.away g ∈ D.awayLevel ∧
          ∀ L : D.domain,
            D.clearedBranchTarget action.shift b L =
              D.totalPeriodMap index variety component cover
                ⟨D.periodMap g L.val, D.periodMap_preserves g L.val L.property⟩
  projector : ∀ h : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q,
    (D.activeH1Complex action active h).comp (D.ballH1ComplexProjector index) =
      (D.ballH1ComplexProjector index).comp (D.activeH1Complex action active h)
  forms : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA
  formsPullback : ∀ h, D.IsRationalFormsPullback (action.algebraAction h) (forms h)
  theta : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA
  canonical : D.IsCanonicalThetaLift hg index (D.totalPeriodMap index variety component cover) theta
  unique : ∀ Ψ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA,
    D.IsCanonicalThetaLift hg index (D.totalPeriodMap index variety component cover) Ψ → Ψ = theta
  covariance : ∀ (h : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (φ : D.sphericalInputs),
    D.activeFormsComplex forms active h (theta φ) = theta (D.sphericalWeilComplex h φ)

theorem exists_witness (h : Theta.CM.Output D hg hq hIsogenyQuotient) :
    Nonempty (Witness D hg hq hIsogenyQuotient) := by
  obtain ⟨A, hA, e, ec, hec, hraw, j, X, c, p, hdim, hp, hb, hproj,
    rho, hrho, theta, ht, hu, hc⟩ := h
  exact ⟨⟨A, hA, e, ec, hec, hraw, j, X, c, p, hdim, hp, hb, hproj,
    rho, hrho, theta, ht, hu, hc⟩⟩

theorem output (W : Witness D hg hq hIsogenyQuotient) : Theta.CM.Output D hg hq hIsogenyQuotient :=
  ⟨W.action, W.realization, W.active, W.activeComplex, W.complexification, W.raw,
    W.index, W.variety, W.component, W.cover, W.dimension, W.uniformization,
    W.branches, W.projector, W.forms, W.formsPullback, W.theta, W.canonical,
    W.unique, W.covariance⟩

theorem nonempty_iff : Nonempty (Witness D hg hq hIsogenyQuotient) ↔ Theta.CM.Output D hg hq hIsogenyQuotient :=
  ⟨fun ⟨W⟩ => output D hg hq hIsogenyQuotient W, exists_witness D hg hq hIsogenyQuotient⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaWitness.CM
