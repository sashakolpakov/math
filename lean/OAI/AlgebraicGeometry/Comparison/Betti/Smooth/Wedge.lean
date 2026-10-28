import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.FormRealization
import OAI.AlgebraicTopology.Kunneth.WedgeAlgebra
import OAI.AlgebraicTopology.Kunneth.ClosedManifoldWedge

/-! # Wedge -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.Wedge

noncomputable section

/-! Exterior multiplication and differentiation in the actual smooth-form model. -/

open ChartedSpace
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {p q n : ℕ}

theorem eq_of_inChart {a b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n}
    (h : ∀ (e : OpenPartialHomeomorph M E), e ∈ atlas E M →
      ∀ y ∈ e.target, a.val.inChart e y = b.val.inChart e y) : a = b := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  let e := chartAt E x
  have he : e ∈ atlas E M := chart_mem_atlas E x
  have hx : x ∈ e.source := mem_chart_source E x
  have hc := h e he (e x) (e.map_source hx)
  exact (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart_inChart_apply e he a.val hx).symm.trans
    ((congrArg (fun c : E [⋀^Fin n]→L[ℝ] ℂ =>
      c.compContinuousLinearMap (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e x)) hc).trans
        (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart_inChart_apply e he b.val hx))

/-- Product rule for a closed right factor in the genuine manifold complex. -/
theorem manifoldWedge_d_rightClosed (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p)
    (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M q) (hb : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b = 0) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a b) =
      AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldDegreeCast (by omega) (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) b) := by
  apply eq_of_inChart
  intro e he y hy
  rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_inChart _ e he hy]
  change extDeriv ((AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge a.val b.val).inChart e) y =
    (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldDegreeCast (by omega)
      (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val b.val)).inChart e y
  rw [AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldDegreeCast_inChart, AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge_inChart, AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge_inChart]
  dsimp only
  rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_inChart a e he hy]
  have hbd : extDeriv (b.val.inChart e) y = 0 := by
    have h := b.d_inChart e he hy
    rw [hb] at h
    change (0 : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (q + 1)).inChart e y = _ at h
    rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_zero] at h
    exact h.symm
  exact AlgebraicTopology.Kunneth.WedgeLeibniz.Constructions.extDeriv_covectorWedge_of_right_closed (a.val.inChart e) (b.val.inChart e) y
    ((Analysis.DifferentialForms.Manifold.Derivative.smoothForm_contDiffAt_inChart a.smooth e he hy).of_le (by simp))
    ((Analysis.DifferentialForms.Manifold.Derivative.smoothForm_contDiffAt_inChart b.smooth e he hy).of_le (by simp)) hbd

/-- The product rule applies to every exact right factor. -/
theorem manifoldWedge_d_exact (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p)
    (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M q) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b)) =
      AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldDegreeCast (by omega)
        (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b)) :=
  manifoldWedge_d_rightClosed a _ (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_squared b)

theorem manifoldWedge_add_left (a a' : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p)
    (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M q) :
    AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge (a + a') b = AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a b + AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a' b := by
  apply eq_of_inChart
  intro e he y hy
  change (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge (a.val + a'.val) b.val).inChart e y =
    (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge a.val b.val + AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge a'.val b.val).inChart e y
  rw [AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge_inChart, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add,
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add, AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge_inChart, AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge_inChart]
  exact AlgebraicTopology.Kunneth.WedgeAlgebra.Constructions.covectorWedge_add_left _ _ _

theorem manifoldWedge_smul_left (c : ℂ) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p)
    (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M q) :
    AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge (c • a) b = c • AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a b := by
  apply eq_of_inChart
  intro e he y hy
  change (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge (c • a.val) b.val).inChart e y =
    (c • AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge a.val b.val).inChart e y
  rw [AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge_inChart, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul,
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul, AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge_inChart]
  exact AlgebraicTopology.Kunneth.WedgeAlgebra.Constructions.covectorWedge_smul_left _ _ _

theorem manifoldWedge_add_right (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p)
    (b b' : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M q) :
    AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a (b + b') = AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a b + AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a b' := by
  apply eq_of_inChart
  intro e he y hy
  change (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge a.val (b.val + b'.val)).inChart e y =
    (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge a.val b.val + AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge a.val b'.val).inChart e y
  rw [AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge_inChart, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add,
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add, AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge_inChart, AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge_inChart]
  exact AlgebraicTopology.Kunneth.WedgeAlgebra.Constructions.covectorWedge_add_right _ _ _

theorem manifoldWedge_smul_right (c : ℂ) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p)
    (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M q) :
    AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a (c • b) = c • AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a b := by
  apply eq_of_inChart
  intro e he y hy
  change (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge a.val (c • b.val)).inChart e y =
    (c • AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge a.val b.val).inChart e y
  rw [AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge_inChart, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul,
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul, AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge_inChart]
  exact AlgebraicTopology.Kunneth.WedgeAlgebra.Constructions.covectorWedge_smul_right _ _ _

theorem covectorWedge_zero_one (a : E [⋀^Fin 0]→L[ℝ] ℂ)
    (b : E [⋀^Fin 1]→L[ℝ] ℂ) : AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge a b = a 0 • b := by
  let : Unique (Equiv.Perm (Fin 1)) :=
    { default := Equiv.refl _
      uniq := fun _ => Subsingleton.elim _ _ }
  ext v
  rw [AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge_apply]
  simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, mul_one,
    inv_one, one_smul, Fintype.sum_unique]
  change 1 • (a (fun i => v (Fin.castAdd 1 i)) * b (fun i => v (Fin.natAdd 0 i))) =
    a 0 * b v
  rw [one_smul]
  congr 1
  · exact congrArg a (Subsingleton.elim _ _)
  · congr 1
    funext i
    exact congrArg v (Fin.ext (Nat.zero_add i.val))

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
@[simp]
theorem manifoldDegreeCast_refl (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldDegreeCast rfl a = a := rfl

variable {A : Type*} [CommRing A] [Algebra ℂ A]
  (φ : A →ₐ[ℂ] C(M, ℂ))
  (hφ : ∀ a : A, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (φ a))

theorem manifoldWedge_zeroForm_one (a : A) (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1) :
    AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge (FormRealization.zeroFormMap φ hφ a) b = Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction (φ a) (hφ a) b := by
  apply eq_of_inChart
  intro e he y hy
  change (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar (φ a)) b.val).inChart e y =
    (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.smulFunction (φ a) b.val).inChart e y
  rw [AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge_inChart, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar_inChart, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smulFunction]
  dsimp only
  exact covectorWedge_zero_one _ _

/-- The unit zero-form is the left unit on one-forms. -/
theorem manifoldWedge_unit_zero_one (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1) :
    AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge (FormRealization.zeroFormMap φ hφ 1) b = b := by
  apply eq_of_inChart
  intro e he y hy
  change (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar (φ 1)) b.val).inChart e y = _
  rw [AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge_inChart, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar_inChart]
  dsimp only
  rw [covectorWedge_zero_one]
  change φ 1 (e.symm y) • b.val.inChart e y = _
  rw [map_one]
  exact one_smul ℂ (b.val.inChart e y)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.Wedge
