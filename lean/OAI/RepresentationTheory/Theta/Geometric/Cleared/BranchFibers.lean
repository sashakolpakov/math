import OAI.RepresentationTheory.Theta.Geometric.Period.DomainTopology

/-! # Branch Fibers -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Continuous branches on the actual negative-line domain are exactly
the points of one source fiber whenever the source is a covering map.
The comparison evaluates the original lift, retaining its scheme point. -/

open _root_.CategoryTheory

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.ClearedBranch.ext {c : D.domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace}
    {a : Intrinsic.Hecke.ActiveWeight} {b d : D.ClearedBranch c a} (h : b.lift = d.lift) : b = d := by
  cases b
  cases d
  cases h
  rfl

def Data.ActiveHeckeThetaData.clearedBranchEvaluation
    {c : D.domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace} {a : Intrinsic.Hecke.ActiveWeight} (x₀ : D.domain)
    (b : D.ClearedBranch c a) :
    {p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints
      (D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).cover //
      p ≫ (D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).source = c x₀} :=
  ⟨b.lift x₀, b.source x₀⟩

theorem Data.ActiveHeckeThetaData.clearedBranchEvaluation_bijective (hg : D.pel.HasIntegralModelGeometry)
    {c : D.domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace} (hc : Continuous c) (a : Intrinsic.Hecke.ActiveWeight)
    (hcover : IsCoveringMap (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
      (D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).source))
    (x₀ : D.domain) : Function.Bijective (D.clearedBranchEvaluation (c := c) (a := a) x₀) := by
  let : SimplyConnectedSpace D.domain := D.domain_simplyConnected hg
  let : LocallyPathConnectedSpace D.domain := D.domain_locallyPathConnected
  constructor
  · intro b d h
    obtain ⟨f, _, huniq⟩ := hcover.existsUnique_continuousMap_lifts ⟨c, hc⟩ x₀ (b.lift x₀) (b.source x₀)
    have hb : b.lift = f := huniq b.lift ⟨rfl, funext b.source⟩
    have hd : d.lift = f := huniq d.lift ⟨(congrArg Subtype.val h).symm, funext d.source⟩
    exact Data.ActiveHeckeThetaData.ClearedBranch.ext D (hb.trans hd.symm)
  · intro p
    obtain ⟨f, hf, _⟩ := hcover.existsUnique_continuousMap_lifts ⟨c, hc⟩ x₀ p.val p.property
    refine ⟨⟨f, fun y => congrFun hf.2 y⟩, ?_⟩
    exact Subtype.ext hf.1

def Data.ActiveHeckeThetaData.clearedBranchFiberEquiv (hg : D.pel.HasIntegralModelGeometry)
    {c : D.domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace} (hc : Continuous c) (a : Intrinsic.Hecke.ActiveWeight)
    (hcover : IsCoveringMap (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
      (D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).source))
    (x₀ : D.domain) : D.ClearedBranch c a ≃
    {p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints
      (D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).cover //
      p ≫ (D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).source = c x₀} :=
  Equiv.ofBijective (D.clearedBranchEvaluation x₀) (D.clearedBranchEvaluation_bijective hg hc a hcover x₀)

theorem Data.ActiveHeckeThetaData.clearedBranchFiberEquiv_apply (hg : D.pel.HasIntegralModelGeometry)
    {c : D.domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace} (hc : Continuous c) (a : Intrinsic.Hecke.ActiveWeight)
    (hcover : IsCoveringMap (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
      (D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).source))
    (x₀ : D.domain) (b : D.ClearedBranch c a) :
    (D.clearedBranchFiberEquiv hg hc a hcover x₀ b).val = b.lift x₀ := rfl

end

end OAI.RepresentationTheory.Theta.Geometric
