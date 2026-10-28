import OAI.RepresentationTheory.Theta.Geometric.Complex.CovectorPurity
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicDerivativeScalars

/-! # Bidegree Cover Reflection -/

namespace OAI.RepresentationTheory.Theta.Geometric.BidegreeCoverReflection

noncomputable section

/-! A surjective holomorphic map with surjective differentials reflects
the actual bidegree of differential forms. -/

set_option backward.isDefEq.respectTransparency false
open scoped _root_.Manifold ContDiff

theorem rawForm_preferred_value {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {n : ℕ} (a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M n) (x : M) :
    a.inChart (chartAt E x) (chartAt E x x) = a x := by
  have hd := mfderivWithin_range_extChartAt_symm (I := 𝓘(ℝ, E)) (x := x)
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_def, id_eq, Set.range_id,
    mfderivWithin_univ] at hd
  ext v
  change a ((chartAt E x).symm (chartAt E x x))
    (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x).symm (chartAt E x x) (v i)) = a x v
  have hv : (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x).symm (chartAt E x x) (v i)) = v := by
    funext i
    exact congrArg (fun b : E →L[ℝ] E => b (v i)) hd
  rw [hv, (chartAt E x).left_inv (mem_chart_source E x)]

theorem manifoldBidegree_iff_pointwise {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
    {p q : ℕ} (a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q)) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M p q a ↔ ∀ x, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q (a x) := by
  let : IsManifold 𝓘(ℝ, E) ∞ M := Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth
  rw [Analysis.DifferentialForms.Manifold.BidegreeInvariant.hasManifoldBidegree_iff_chartAt]
  exact forall_congr' fun x => by rw [rawForm_preferred_value]

theorem bidegree_of_surjective_pullback {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
    {p q : ℕ} (a : Analysis.DifferentialForms.Manifold.Basic.FormValue F (p + q)) (f : E →L[ℂ] F) (hf : Function.Surjective f)
    (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q (a.compContinuousLinearMap (f.restrictScalars ℝ))) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree F p q a := by
  intro z v
  choose u hu using fun i => hf (v i)
  have h := ha z u
  change a (fun i => f ((z : ℂ) • u i)) = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z * a (fun i => f (u i)) at h
  simpa only [map_smul, hu] using h

theorem manifoldBidegree_of_surjective_pullback {E F M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ∞ N]
    {p q : ℕ} (a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm F N (p + q))
    (f : M → N) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) 1 f)
    (hs : Function.Surjective f)
    (hd : ∀ x, Function.Surjective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x))
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M p q (a.pullback (E := E) f)) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree F N p q a := by
  apply (manifoldBidegree_iff_pointwise a).mpr
  intro y
  obtain ⟨x, rfl⟩ := hs y
  apply bidegree_of_surjective_pullback (E := E) (F := F) (a (f x))
    (show E →L[ℂ] F from mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x) (hd x)
  have h := (manifoldBidegree_iff_pointwise (a.pullback (E := E) f)).mp ha x
  have he := congrArg (fun b : E →L[ℝ] F => (a (f x)).compContinuousLinearMap b)
    (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicDerivativeScalars.real_mfderiv_eq_complex_restrictScalars (hf x))
  exact he ▸ h

end

end OAI.RepresentationTheory.Theta.Geometric.BidegreeCoverReflection
