import OAI.RepresentationTheory.Hecke.RadialDilation.TensorCommutant
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Compact
import OAI.RepresentationTheory.Hecke.RadialDilation.TensorAction

/-! # Tensor Span -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.TensorSpan

noncomputable section

/-! Pure-tensor decomposition retains actual slices of the original test
function. Consequently integral SL3 invariance forces every local factor
to lie in the radial input space. -/

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]

theorem test_tensor_expansion_with_sections (f : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (X × Y)) :
    ∃ r : Finset (RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace X), ∃ g : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace X → RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace Y,
      f = ∑ v ∈ r, RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest v (g v) ∧
        ∀ v ∈ r, ∃ y, RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.testSection y f = v := by
  let s := fun y => RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.testSection y f
  let r := (RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.testSection_range_finite f).toFinset
  let g := RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.testFiberCoefficient s (RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.testSection_locallyConstant f) (RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.testSection_compactSupport f)
  refine ⟨r, g, ?_, ?_⟩
  swap
  · intro v hv
    exact (RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.testSection_range_finite f).mem_toFinset.mp hv
  apply Subtype.ext
  funext p
  change f.val (p.1, p.2) = (∑ v ∈ r, RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest v (g v)).val (p.1, p.2)
  simp only [Submodule.coe_sum, Finset.sum_apply, RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest_apply]
  change f.val (p.1, p.2) = ∑ v ∈ r, v.val p.1 *
    (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.testFiberCoefficient s (RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.testSection_locallyConstant f) (RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.testSection_compactSupport f) v).val p.2
  simp_rw [RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.testFiberCoefficient_apply]
  rw [Finset.sum_eq_single (s p.2)]
  · simp only [ite_true]
    by_cases hz : s p.2 = 0
    · rw [ite_eq_left hz, mul_zero]
      exact congrArg (fun v : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace X => v.val p.1) hz
    · rw [ite_eq_right hz, mul_one]
      rfl
  · intro v _ hv
    rw [ite_eq_right (Ne.symm hv), mul_zero]
  · intro hs
    exact (hs ((RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.testSection_range_finite f).mem_toFinset.mpr ⟨p.2, rfl⟩)).elim

theorem integral_fixed_tensor_mem_span (q : ℕ) [Fact q.Prime]
    (f : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q × Y))
    (hf : ∀ g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q, g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q →
      ∀ (x : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q) (y : Y), f.val ((g⁻¹).val.mulVec x, y) = f.val (x, y)) :
    f ∈ Submodule.span ℂ {F | ∃ (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) (φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace Y),
      F = RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest (RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization.radialTest q b) φ} := by
  have hsection (y : Y) : (RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.testSection y f).val ∈ RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q := by
    have hfix : (RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.testSection y f).val ∈
        RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (Hecke.matrixSubstitution q) := by
      intro g hg
      funext x
      change f.val ((↑((Matrix.SpecialLinearGroup.toGL g)⁻¹) :
        Matrix (Fin 3) (Fin 3) ℚ_[q]).mulVec x, y) = f.val (x, y)
      rw [← map_inv]
      exact hf g hg x y
    exact Compact.integral_fixed_compact_mem q ⟨(RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.testSection y f).val, hfix⟩
      (RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.testSection y f).property.1 (RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.testSection y f).property.2
  obtain ⟨r, φ, he, hr⟩ := test_tensor_expansion_with_sections f
  rw [he]
  apply Submodule.sum_mem
  intro a ha
  obtain ⟨y, hy⟩ := hr a ha
  have haRadial : a.val ∈ RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q := hy ▸ hsection y
  exact Submodule.subset_span ⟨⟨a.val, haRadial⟩, φ a, rfl⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.TensorSpan
