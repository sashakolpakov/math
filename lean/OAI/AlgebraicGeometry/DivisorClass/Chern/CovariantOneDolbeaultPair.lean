import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CovariantOneAdjointIntegral
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CovariantAntiPair
import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldDolbeault

/-! # Covariant One Dolbeault Pair -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Pairing the original covariant derivative with (0,2) forms gives precisely the original bundle Dolbeault pairing. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

section Open

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {U : Opens M}

omit [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem CovariantOneDolbeaultPair.openManifoldWedge_holo_anti (A a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1)
    (hA : Chern.Open.ManifoldBidegree.OpenManifoldHasBidegree 1 0 A) (ha : Chern.Open.ManifoldBidegree.OpenManifoldHasBidegree 0 1 a) :
    Chern.Open.ManifoldBidegree.OpenManifoldHasBidegree 1 1 (Chern.Open.ManifoldWedge.openManifoldWedge A a) := by
  intro e he y hy c v
  rw [Chern.Open.ManifoldWedge.openManifoldWedge_inChart A a e hy.2]
  simp only [OneFormWedgeEvaluation.covectorWedge_one_one_apply]
  rw [hA e he y hy c (fun _ => v 0), ha e he y hy c (fun _ => v 1),
    hA e he y hy c (fun _ => v 1), ha e he y hy c (fun _ => v 0)]
  simp only [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_one, pow_zero, mul_one, one_mul]
  ring

theorem CovariantOneDolbeaultPair.openConnectionDerivativeOne_minus_dolbeault_mixed (A a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1)
    (hA : Chern.Open.ManifoldBidegree.OpenManifoldHasBidegree 1 0 A) (ha : Chern.Open.ManifoldBidegree.OpenManifoldHasBidegree 0 1 a) :
    Chern.Open.ManifoldBidegree.OpenManifoldHasBidegree 1 1 (Chern.Open.ConnectionCurvature.openConnectionDerivativeOne A a - Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD 0 1 1 a) := by
  have he : Chern.Open.ConnectionCurvature.openConnectionDerivativeOne A a - Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD 0 1 1 a =
      Chern.Open.ManifoldDolbeault.openManifoldDolbeaultPrime 0 1 1 a + Chern.Open.ManifoldWedge.openManifoldWedge A a := by
    rw [Chern.Open.ConnectionCurvature.openConnectionDerivativeOne_apply, ← Chern.Open.ManifoldDolbeault.openManifoldDolbeaultPrime_add_dbar 0 1 a]
    abel
  rw [he]
  exact Chern.Open.ManifoldDolbeault.openManifoldHasBidegree_add (Chern.Open.ManifoldDolbeault.openManifoldDolbeaultPrime_hasBidegree rfl ha)
    (CovariantOneDolbeaultPair.openManifoldWedge_holo_anti A a hA ha)

end Open

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

theorem CovariantOneDolbeaultPair.projectiveOpenFormPair_covariantOne_dolbeault {W : Opens V.analyticSpace}
    (A a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel W 1) (b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel W 2)
    (hA : Chern.Open.ManifoldBidegree.OpenManifoldHasBidegree 1 0 A) (ha : Chern.Open.ManifoldBidegree.OpenManifoldHasBidegree 0 1 a)
    (hb : Chern.Open.ManifoldBidegree.OpenManifoldHasBidegree 0 2 b) (y : W) :
    Projective.CovectorPair.projectiveTangentCovectorPair V 2 y.val (b y) (Chern.Open.ConnectionCurvature.openConnectionDerivativeOne A a y) =
      Projective.CovectorPair.projectiveTangentCovectorPair V 2 y.val (b y) (Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD 0 1 1 a y) := by
  let d := Chern.Open.ConnectionCurvature.openConnectionDerivativeOne A a - Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD 0 1 1 a
  have hd : Chern.Open.ManifoldBidegree.OpenManifoldHasBidegree 1 1 d := CovariantOneDolbeaultPair.openConnectionDerivativeOne_minus_dolbeault_mixed A a hA ha
  have hz := Chern.Open.FormOrthogonality.projectiveOpenFormPair_pure_orthogonal V 2 ⟨(0, 2), rfl⟩ ⟨(1, 1), rfl⟩
    (by decide) b d hb hd y
  have he : Chern.Open.ConnectionCurvature.openConnectionDerivativeOne A a y = Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD 0 1 1 a y + d y := by
    change Chern.Open.ConnectionCurvature.openConnectionDerivativeOne A a y = Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD 0 1 1 a y +
      (Chern.Open.ConnectionCurvature.openConnectionDerivativeOne A a y - Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD 0 1 1 a y)
    exact (add_comm _ _).trans (sub_add_cancel _ _) |>.symm
  rw [he, Chern.Open.FormOrthogonality.projectiveTangentCovectorPair_add_right, hz, add_zero]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.covariantDerivativeOne_dolbeault_point_pair
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) (b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 2) (x : V.analyticSpace) :
    h.globalFormPair V 2 b.val (h.covariantDerivativeOne ⊤ a.val) x =
      h.globalFormPair V 2 b.val (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val x := by
  have hx := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace u).mem_domain x
  let W := (⊤ : Opens V.analyticSpace) ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u x
  let y : W := ⟨x, trivial, hx⟩
  let A := Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (show W ≤ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u x from inf_le_right) (h.localConnection x)
  have hp : Chern.Open.ManifoldBidegree.OpenManifoldHasBidegree 1 0 (h.localConnection x) :=
    Manifold.OneFormProjection.openManifoldOnePart_holomorphic (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm (h.logFunction x)))
  have hA : Chern.Open.ManifoldBidegree.OpenManifoldHasBidegree 1 0 A := Chern.Open.ManifoldBidegree.openManifoldHasBidegree_restrict inf_le_right hp
  have hpair := CovariantOneDolbeaultPair.projectiveOpenFormPair_covariantOne_dolbeault V A (a.val.val x) (b.val.val x) hA (a.property x) (b.property x) y
  rw [h.globalFormPair_inFrame V 2 b.val _ x x hx, h.globalFormPair_inFrame V 2 b.val _ x x hx]
  exact congrArg (fun z : ℂ => (h.weight x ⟨x, hx⟩ : ℂ) * z) hpair

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.covariantDerivativeOne_dolbeault_pair
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) (b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 2) :
    h.formIntegralPair V 2 b.val (h.covariantDerivativeOne ⊤ a.val) =
      h.formIntegralPair V 1 (h.degreeCodifferential V 1 b.val) a.val := by
  have hp : h.formIntegralPair V 2 b.val (h.covariantDerivativeOne ⊤ a.val) =
      h.formIntegralPair V 2 b.val (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (h.covariantDerivativeOne_dolbeault_point_pair V a b))
  exact hp.trans (h.degreeCodifferential_pair V 1 a b.val)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
