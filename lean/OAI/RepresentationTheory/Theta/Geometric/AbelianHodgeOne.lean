import OAI.AlgebraicGeometry.AbelianVariety.PureAverage
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectivePurePullback
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveNaturality
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveHodgeNaturality

/-! # Abelian Hodge One -/

namespace OAI.RepresentationTheory.Theta.Geometric.AbelianHodgeOne

noncomputable section

/-! Actual abelian H¹ splits into its two degree-one types by the explicit
covector projections. Injective algebraic pullback reflects holomorphic type. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction

theorem projectivePureH1_disjoint (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Disjoint (V.pureBettiSubspace 1 0) (V.pureBettiSubspace 0 1) := by
  apply Submodule.disjoint_def.mpr
  intro c hc hd
  obtain ⟨x, hx, hxc⟩ := hc
  obtain ⟨y, hy, hyc⟩ := hd
  have hxy : x = y := (V.deRhamBettiIso 1).toLinearEquiv.injective (hxc.trans hyc.symm)
  have hz : x = 0 := Submodule.disjoint_def.mp
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Intersection.CM.Construction.pureDeRham_one_disjoint (E := V.analyticModel) (M := V.analyticSpace))
      x hx (hxy.symm ▸ hy)
  rw [← hxc, hz, map_zero]

theorem abelianPureH1_sup_top (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    A.variety.pureBettiSubspace 1 0 ⊔ A.variety.pureBettiSubspace 0 1 = ⊤ := by
  apply top_unique
  intro a _
  let e := AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv A 1
  let v := e.symm a
  let w := Complex.I • v.compContinuousLinearMap
    (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)
  let h := (1 / 2 : ℂ) • (v - w)
  let b := (1 / 2 : ℂ) • (v + w)
  have hh : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree A.variety.analyticModel 1 0 h := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.oneCovector_holomorphic_projection v
  have hb : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree A.variety.analyticModel 0 1 b := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.oneCovector_antiholomorphic_projection v
  have hsum : h + b = v := by dsimp [h, b]; module
  apply Submodule.mem_sup.mpr
  refine ⟨e h, (AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv_pure A 1 0 h).mpr hh,
    e b, (AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv_pure A 0 1 b).mpr hb, ?_⟩
  rw [← map_add, hsum]
  exact e.apply_symm_apply a

theorem abelianPullback_holomorphic_reflection (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ A.toOver)
    (hf : Function.Injective (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f))
    (a : A.variety.complexCohomology 1)
    (ha : AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f a ∈ X.pureBettiSubspace 1 0) :
    a ∈ A.variety.pureBettiSubspace 1 0 := by
  have hall : a ∈ A.variety.pureBettiSubspace 1 0 ⊔ A.variety.pureBettiSubspace 0 1 := by
    rw [abelianPureH1_sup_top]; trivial
  obtain ⟨h, hh, b, hb, hab⟩ := Submodule.mem_sup.mp hall
  have hfh := AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_mem_pureBettiSubspace f 1 0 hh
  have hfb := AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_mem_pureBettiSubspace f 0 1 hb
  have hb10 : AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f b ∈ X.pureBettiSubspace 1 0 := by
    have ht := (X.pureBettiSubspace 1 0).sub_mem ha hfh
    rw [← hab, map_add, add_sub_cancel_left] at ht
    exact ht
  have hb0 : AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f b = 0 :=
    Submodule.disjoint_def.mp (projectivePureH1_disjoint X) _ hb10 hfb
  have hz : b = 0 := hf (hb0.trans (map_zero _).symm)
  rw [hz, add_zero] at hab
  exact hab ▸ hh

end

end OAI.RepresentationTheory.Theta.Geometric.AbelianHodgeOne
