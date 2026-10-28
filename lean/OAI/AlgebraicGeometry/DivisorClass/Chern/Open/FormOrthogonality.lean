import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CovectorPair
import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.OneFormProjection
import OAI.Analysis.HodgeTheory.Decomposition.GlobalOrthogonality

/-! # Form Orthogonality -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Open.FormOrthogonality

noncomputable section

/-! The original projective metric makes distinct local types orthogonal;
the genuine antiholomorphic one-form projection is self-adjoint. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.GlobalOrthogonality.Constructions
attribute [local instance] NormedSpace.complexToReal

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem projectiveOpenFormPair_pure_orthogonal {U : Opens V.analyticSpace} (n : ℕ)
    (i j : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n) (hij : i ≠ j) (a b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U n)
    (ha : ManifoldBidegree.OpenManifoldHasBidegree i.val.1 i.val.2 a)
    (hb : ManifoldBidegree.OpenManifoldHasBidegree j.val.1 j.val.2 b) (x : U) :
    Projective.CovectorPair.projectiveTangentCovectorPair V n x.val (a x) (b x) = 0 := by
  let e := chartAt V.analyticModel x.val
  have he := chart_mem_atlas V.analyticModel x.val
  have hx := mem_chart_source V.analyticModel x.val
  have hy : e x.val ∈ Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e (U : Set V.analyticSpace) :=
    ⟨e.map_source hx, by
      change e.symm (e x.val) ∈ U
      rw [e.left_inv hx]
      exact x.property⟩
  have h := Projective.CovectorPair.projectiveFormPointPair_eq_tangentPair V n x.val a.extension b.extension
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply a x, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply b x] at h
  rw [← h, Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair_eq_chart V e he x.val hx]
  exact Analysis.HodgeTheory.Decomposition.GlobalOrthogonality.Constructions.projectiveChartFormPair_pure_orthogonal V e he (e x.val) (e.map_source hx) n i j hij
    (a.extension.inChart e (e x.val)) (b.extension.inChart e (e x.val))
    (ha e he (e x.val) hy) (hb e he (e x.val) hy)

theorem projectiveTangentCovectorPair_add_right (n : ℕ) (x : V.analyticSpace)
    (a b c : TangentSpace 𝓘(ℝ, V.analyticModel) x [⋀^Fin n]→L[ℝ] ℂ) :
    Projective.CovectorPair.projectiveTangentCovectorPair V n x a (b + c) =
      Projective.CovectorPair.projectiveTangentCovectorPair V n x a b + Projective.CovectorPair.projectiveTangentCovectorPair V n x a c := by
  calc
    _ = star (Projective.CovectorPair.projectiveTangentCovectorPair V n x (b + c) a) :=
      (Projective.CovectorPair.projectiveTangentCovectorPair_symm V n x a (b + c)).symm
    _ = _ := by
      rw [Projective.CovectorPair.projectiveTangentCovectorPair_add_left, star_add]
      change (starRingEnd ℂ) (Projective.CovectorPair.projectiveTangentCovectorPair V n x b a) +
        (starRingEnd ℂ) (Projective.CovectorPair.projectiveTangentCovectorPair V n x c a) = _
      rw [Projective.CovectorPair.projectiveTangentCovectorPair_symm,
        Projective.CovectorPair.projectiveTangentCovectorPair_symm]

theorem projectiveOpenFormPair_anti_holo {U : Opens V.analyticSpace}
    (a b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U 1)
    (ha : ManifoldBidegree.OpenManifoldHasBidegree 0 1 a) (hb : ManifoldBidegree.OpenManifoldHasBidegree 1 0 b) (x : U) :
    Projective.CovectorPair.projectiveTangentCovectorPair V 1 x.val (a x) (b x) = 0 :=
  projectiveOpenFormPair_pure_orthogonal V 1 ⟨(0, 1), rfl⟩ ⟨(1, 0), rfl⟩ (by decide) a b ha hb x

theorem projectiveOpenFormPair_anti_projection {U : Opens V.analyticSpace}
    (a b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U 1)
    (ha : ManifoldBidegree.OpenManifoldHasBidegree 0 1 a) (x : U) :
    Projective.CovectorPair.projectiveTangentCovectorPair V 1 x.val (a x) (Manifold.OneFormProjection.openManifoldOnePart Complex.I b x) =
      Projective.CovectorPair.projectiveTangentCovectorPair V 1 x.val (a x) (b x) := by
  have hd := congrArg (fun c : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U 1 => c x)
    (Manifold.OneFormProjection.openManifoldOnePart_add b)
  have hz := projectiveOpenFormPair_anti_holo V a (Manifold.OneFormProjection.openManifoldOnePart (-Complex.I) b)
    ha (Manifold.OneFormProjection.openManifoldOnePart_holomorphic b) x
  calc
    _ = Projective.CovectorPair.projectiveTangentCovectorPair V 1 x.val (a x)
        (Manifold.OneFormProjection.openManifoldOnePart (-Complex.I) b x + Manifold.OneFormProjection.openManifoldOnePart Complex.I b x) := by
      rw [projectiveTangentCovectorPair_add_right, hz, zero_add]
    _ = _ := congrArg (Projective.CovectorPair.projectiveTangentCovectorPair V 1 x.val (a x)) hd

theorem projectiveOpenFormPair_dbar {U : Opens V.analyticSpace}
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U 1)
    (b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U 0)
    (ha : ManifoldBidegree.OpenManifoldHasBidegree 0 1 a) (x : U) :
    Projective.CovectorPair.projectiveTangentCovectorPair V 1 x.val (a x) (ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 b x) =
      Projective.CovectorPair.projectiveTangentCovectorPair V 1 x.val (a x) (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d b x) := by
  rw [← Manifold.OneFormProjection.openManifoldOnePart_d]
  exact projectiveOpenFormPair_anti_projection V a (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d b) ha x

theorem projectiveOpenFormPair_anti_selfAdjoint {U : Opens V.analyticSpace}
    (a b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U 1) (x : U) :
    Projective.CovectorPair.projectiveTangentCovectorPair V 1 x.val (Manifold.OneFormProjection.openManifoldOnePart Complex.I a x) (b x) =
      Projective.CovectorPair.projectiveTangentCovectorPair V 1 x.val (a x) (Manifold.OneFormProjection.openManifoldOnePart Complex.I b x) := by
  have ha := projectiveOpenFormPair_anti_projection V (Manifold.OneFormProjection.openManifoldOnePart Complex.I a) b
    (Manifold.OneFormProjection.openManifoldOnePart_antiholomorphic a) x
  have hb := projectiveOpenFormPair_anti_projection V (Manifold.OneFormProjection.openManifoldOnePart Complex.I b) a
    (Manifold.OneFormProjection.openManifoldOnePart_antiholomorphic b) x
  have hc := congrArg (starRingEnd ℂ) hb
  rw [Projective.CovectorPair.projectiveTangentCovectorPair_symm, Projective.CovectorPair.projectiveTangentCovectorPair_symm] at hc
  exact ha.symm.trans hc

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Open.FormOrthogonality
