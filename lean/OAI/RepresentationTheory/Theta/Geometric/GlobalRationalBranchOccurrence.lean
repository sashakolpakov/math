import OAI.RepresentationTheory.Theta.Geometric.PointwiseRationalBranches
import OAI.RepresentationTheory.Theta.Geometric.Projective.ModelSelection
import OAI.RepresentationTheory.Theta.Geometric.Active.BranchTraceModels
import OAI.RepresentationTheory.Theta.Geometric.Rational.DomainSmooth

/-! # Global Rational Branch Occurrence -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! A prescribed rational active target is realized by one actual
continuous cleared branch over the entire original ball. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold ContDiff

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (A : TateComparison.Action D.pel)
    (hA : A.IsRealization D.pel hg hgood hIsogenyQuotient)
    (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
    (hc : D.HasFiniteCoordinates)
    (j : Fin D.pel.componentCount) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ D.componentComplex j) (cover : D.domain → X.analyticSpace)
    (hcover : D.IsPeriodUniformization X cover)
    (href : ∀ x, D.totalPeriodMap j X component cover x = D.referenceModuliMap hg x)

include hA hdegree hs hc hcover href in
theorem Data.ActiveHeckeThetaData.global_rational_cleared_branch
    (a : Intrinsic.Hecke.ActiveWeight) (g : D.RationalSU) (haway : D.away g ∈ D.awayLevel)
    (hcos : DoubleCosets.Spherical.InDoubleCoset (SphericalGU.Spherical.integralSL3 q)
      (Intrinsic.Hecke.activeSLRepresentative q a)⁻¹ (D.activeLocal g)⁻¹) :
    ∃ b : D.ClearedBranch (D.totalPeriodMap j X component cover) a,
      ∀ x, D.clearedBranchTarget A.shift b x =
        D.totalPeriodMap j X component cover (D.rationalPeriodPoint g x) := by
  let c := D.totalPeriodMap j X component cover
  have hcont : Continuous c := D.totalPeriodMap_continuous j X component cover hcover.2.1.continuous
  let : Finite (D.ClearedBranch c a) := D.clearedBranch_finite hg hcont a
  let : Fintype (D.ClearedBranch c a) := Fintype.ofFinite _
  let : ContractibleSpace D.domain := D.domain_contractible hg
  let : Nonempty D.domain := ⟨D.domainOrigin hg⟩
  obtain ⟨Y, target, l, hl, hpoint, _⟩ :=
    D.exists_activeBranchTrace_models hg hgood hIsogenyQuotient A hA j X component cover hcover a
  have hcov := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable hcover.2.2.1
  obtain ⟨b, hb⟩ := Projective.ModelSelection.projective_model_countable_selection D.domain
    (isPreconnected_iff_preconnectedSpace.mpr inferInstance)
    (D.complexSpaceProjectivePresentation hg) X
    (component.hom ≫ D.componentComplexInclusion j)
    (cover ∘ D.rationalPeriodPoint g)
    ((hcov.comp (D.rationalPeriodPoint_contMDiff g)).of_le (by simp))
    Y target l (fun b => (hl b).of_le (by simp)) (fun x => by
      obtain ⟨b, hb⟩ := D.pointwise_rational_cleared_branch hg hgood hIsogenyQuotient A hA hdegree hs hc
        hcont href a g haway hcos x
      exact ⟨b, hb.symm.trans (hpoint b x).symm⟩)
  exact ⟨b, fun x => (hpoint b x).symm.trans (hb x).symm⟩

end

end OAI.RepresentationTheory.Theta.Geometric
