import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.AntiForms
import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.OneFormProjection
import OAI.Analysis.DifferentialForms.Manifold.SectionCoordinates

/-! # One Form Projection -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OneFormProjection

noncomputable section

/-! The genuine type projection on one-forms with values in the original bundle. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {U : Opens M}

theorem openManifoldOnePart_apply (c : ℂ) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1) (x : U) :
    Manifold.OneFormProjection.openManifoldOnePart c a x = (1 / 2 : ℂ) • (a x + c • (a x).compContinuousLinearMap
      (Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentScalarMap (x : M) Complex.I)) := by
  change (1 / 2 : ℂ) • (a x + c • Open.ManifoldAction.openManifoldComplexAction AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹ a x) = _
  rw [Open.ManifoldAction.openManifoldComplexAction_apply, inv_inv, AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit_coe]

theorem openManifoldOnePart_eq_of_anti (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1)
    (ha : Open.ManifoldBidegree.OpenManifoldHasBidegree 0 1 a) : Manifold.OneFormProjection.openManifoldOnePart Complex.I a = a := by
  apply sub_eq_zero.mp
  apply (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.eq_zero_iff_inChartOn U _).mpr
  intro e he
  rw [map_sub]
  apply sub_eq_zero.mpr
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro y
  change (Manifold.OneFormProjection.openManifoldOnePart Complex.I a).extension.inChart e y = a.extension.inChart e y
  rw [Manifold.OneFormProjection.openManifoldOnePart_inChart _ a e he y.property]
  ext v
  have h := ha e he y y.property AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit v
  simp only [AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit_coe, Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_zero, pow_one, one_mul,
    Complex.star_def, Complex.conj_I] at h
  change (1 / 2 : ℂ) * (a.extension.inChart e y v + Complex.I *
    a.extension.inChart e y (fun i => Complex.I • v i)) = a.extension.inChart e y v
  rw [h]
  ring_nf
  rw [Complex.I_sq]
  ring

variable (u : Connecting.holomorphicUnitCohomology E M) (U : Opens M)

def holomorphicLineOnePart (c : ℂ) :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 1 →ₗ[ℂ] HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 1 where
  toFun a := ⟨fun i => Manifold.OneFormProjection.openManifoldOnePart c (a.val i), by
    intro i j x hx hi hj
    rw [openManifoldOnePart_apply, openManifoldOnePart_apply, a.property i j x hx hi hj]
    ext v
    simp only [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.compContinuousLinearMap_apply, smul_eq_mul]
    ring⟩
  map_add' a b := by
    apply Subtype.ext
    funext i
    exact (Manifold.OneFormProjection.openManifoldOnePart c).map_add (a.val i) (b.val i)
  map_smul' z a := by
    apply Subtype.ext
    funext i
    exact (Manifold.OneFormProjection.openManifoldOnePart c).map_smul z (a.val i)

theorem holomorphicLineOnePart_coordinate (c : ℂ) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 1) (i : M) :
    (holomorphicLineOnePart u U c a).val i = Manifold.OneFormProjection.openManifoldOnePart c (a.val i) := rfl

theorem holomorphicLineOnePart_anti (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 1) :
    holomorphicLineOnePart u U Complex.I a ∈ HolomorphicLine.AntiForms.holomorphicLineAntiFormSubmodule u U 1 :=
  fun i => Manifold.OneFormProjection.openManifoldOnePart_antiholomorphic (a.val i)

theorem holomorphicLineOnePart_eq_of_anti (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 1)
    (ha : a ∈ HolomorphicLine.AntiForms.holomorphicLineAntiFormSubmodule u U 1) : holomorphicLineOnePart u U Complex.I a = a := by
  apply Subtype.ext
  funext i
  exact openManifoldOnePart_eq_of_anti (a.val i) (ha i)

theorem holomorphicLineOnePart_idempotent (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 1) :
    holomorphicLineOnePart u U Complex.I (holomorphicLineOnePart u U Complex.I a) =
      holomorphicLineOnePart u U Complex.I a :=
  holomorphicLineOnePart_eq_of_anti u U _ (holomorphicLineOnePart_anti u U a)

def holomorphicLineOneAntiProjection :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 1 →ₗ[ℂ] HolomorphicLine.AntiForms.HolomorphicLineAntiForm u U 1 :=
  (holomorphicLineOnePart u U Complex.I).codRestrict _ (holomorphicLineOnePart_anti u U)

theorem holomorphicLineOnePart_range :
    LinearMap.range (holomorphicLineOnePart u U Complex.I) = HolomorphicLine.AntiForms.holomorphicLineAntiFormSubmodule u U 1 := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact holomorphicLineOnePart_anti u U b
  · intro ha
    exact ⟨a, holomorphicLineOnePart_eq_of_anti u U a ha⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OneFormProjection
