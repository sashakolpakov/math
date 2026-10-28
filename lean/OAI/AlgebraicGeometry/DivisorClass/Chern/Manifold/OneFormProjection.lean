import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldDolbeault

/-! # One Form Projection -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.OneFormProjection

noncomputable section

/-! The actual holomorphic and antiholomorphic parts of an arbitrary open manifold one-form. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

theorem oneCovector_holomorphic_part (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 0 ((1 / 2 : ℂ) • (a + (-Complex.I) •
      a.compContinuousLinearMap (ContinuousLinearMap.lsmul ℝ ℂ Complex.I))) := by
  obtain ⟨D, rfl⟩ := (ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ (0 : Fin 1)).surjective a
  have heq : (1 / 2 : ℂ) • ((ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ (0 : Fin 1)) D +
      (-Complex.I) • ((ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ (0 : Fin 1)) D).compContinuousLinearMap
        (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)) =
      (ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ (0 : Fin 1)) (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM E ℂ D) := by
    ext v
    change (1 / 2 : ℂ) * (D (v 0) + (-Complex.I) * D (Complex.I • v 0)) =
      (1 / 2 : ℂ) * (D (v 0) - Complex.I * D (Complex.I • v 0))
    ring
  rw [heq]
  intro z v
  change Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM E ℂ D ((z : ℂ) • v 0) =
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 1 0 z * Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM E ℂ D (v 0)
  simpa only [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_one, pow_zero, mul_one, smul_eq_mul] using
    Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM_apply_smul E ℂ D (z : ℂ) (v 0)

theorem oneCovector_antiholomorphic_part (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 1 ((1 / 2 : ℂ) • (a + Complex.I •
      a.compContinuousLinearMap (ContinuousLinearMap.lsmul ℝ ℂ Complex.I))) := by
  obtain ⟨D, rfl⟩ := (ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ (0 : Fin 1)).surjective a
  intro z v
  change Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ D ((z : ℂ) • v 0) =
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 0 1 z * Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ D (v 0)
  simpa only [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_one, pow_zero, one_mul, smul_eq_mul] using
    Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply_smul E ℂ D (z : ℂ) (v 0)

variable {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {U V : Opens M}

def openManifoldOnePart (c : ℂ) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1 →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1 :=
  (1 / 2 : ℂ) • ((LinearMap.id : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1 →ₗ[ℂ] _) +
    c • Open.ManifoldAction.openManifoldComplexAction AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹)

theorem openManifoldOnePart_restrict (c : ℂ) (h : V ≤ U)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h (openManifoldOnePart c a) =
      openManifoldOnePart c (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h a) := by
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h ((1 / 2 : ℂ) •
    (a + c • Open.ManifoldAction.openManifoldComplexAction AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹ a)) = _
  rw [map_smul, map_add, map_smul, Open.ManifoldAction.openManifoldComplexAction_restrict]
  rfl

theorem openManifoldOnePart_inChart (c : ℂ) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E}
    (hy : y ∈ Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e (U : Set M)) :
    (openManifoldOnePart c a).extension.inChart e y =
      (1 / 2 : ℂ) • (a.extension.inChart e y + c •
        (a.extension.inChart e y).compContinuousLinearMap (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)) := by
  change ((1 / 2 : ℂ) • (a + c • Open.ManifoldAction.openManifoldComplexAction AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹ a)).extension.inChart e y = _
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_smul, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_add,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_smul, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul,
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul]
  simp only [Pi.smul_apply, Pi.add_apply, Open.ManifoldAction.openManifoldComplexAction_inChart _ _ e he hy,
    inv_inv, AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit_coe]

theorem openManifoldOnePart_holomorphic (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1) :
    Open.ManifoldBidegree.OpenManifoldHasBidegree 1 0 (openManifoldOnePart (-Complex.I) a) := by
  intro e he y hy
  rw [openManifoldOnePart_inChart _ a e he hy]
  exact oneCovector_holomorphic_part _

theorem openManifoldOnePart_antiholomorphic (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1) :
    Open.ManifoldBidegree.OpenManifoldHasBidegree 0 1 (openManifoldOnePart Complex.I a) := by
  intro e he y hy
  rw [openManifoldOnePart_inChart _ a e he hy]
  exact oneCovector_antiholomorphic_part _

theorem openManifoldOnePart_add (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1) :
    openManifoldOnePart (-Complex.I) a + openManifoldOnePart Complex.I a = a := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  ext v
  change (1 / 2 : ℂ) * (a x v + (-Complex.I) * _) +
    (1 / 2 : ℂ) * (a x v + Complex.I * _) = a x v
  ring

theorem openManifoldOnePart_d (f : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0) :
    openManifoldOnePart Complex.I (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d f) = Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 f := by
  have hc : -(AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter 0 0)⁻¹ = Complex.I := by
    simp [AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter, Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit_coe, Complex.inv_I]
  rw [Open.ManifoldDolbeault.openManifoldDolbeaultD_apply, hc]
  rfl

def openManifoldOneAntiProjection : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1 →ₗ[ℂ] Open.ManifoldBidegree.AntiOpenManifoldForm E U 1 :=
  (openManifoldOnePart Complex.I).codRestrict _ openManifoldOnePart_antiholomorphic

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.OneFormProjection
