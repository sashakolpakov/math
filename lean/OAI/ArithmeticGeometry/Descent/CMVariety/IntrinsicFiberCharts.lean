import OAI.ArithmeticGeometry.Descent.CMVariety.FiberSliceCharts
import OAI.ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints

/-! # Intrinsic Fiber Charts -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberCharts.Abelian.FamilyPoints

noncomputable section

/-!
Transport a slice of an actual native product chart to the actual scheme
base-change fiber. The chart carrier is the complex-point space of the
scheme pullback, using its proved homeomorphism with the topological fiber.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical

variable {X S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {P V : Type}
  [TopologicalSpace P] [TopologicalSpace V]

/-- The slice chart lives on the literal scheme fiber, and its forward
and inverse maps agree with restriction of the native total-space chart. -/
theorem exists_native_fiber_chart (p : X ⟶ S) (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (q₀ : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AbelianFamilyPoints.FamilyPoints.fiber p s))
    (b : OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) P)
    (e : OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (P × V))
    (hb : s ∈ b.source)
    (hq : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) q₀ ∈ e.source)
    (hmap : ∀ x ∈ e.source, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p x ∈ b.source)
    (hproj : ∀ x ∈ e.source, (e x).1 = b (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p x)) :
    ∃ c : OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AbelianFamilyPoints.FamilyPoints.fiber p s)) V,
      q₀ ∈ c.source ∧
      c.target = {v | (b s, v) ∈ e.target} ∧
      (∀ q, c q = (e (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) q)).2) ∧
      ∀ v ∈ c.target, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) (c.symm v) =
        e.symm (b s, v) := by
  let x₀ := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) q₀
  have hx₀ : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p x₀ = s := (AbelianFamilyPoints.FamilyPoints.fiberHomeomorph p s q₀).property
  have hb₀ : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p x₀ ∈ b.source := hx₀ ▸ hb
  obtain ⟨c, hc, _, ht, hf, hi⟩ := FiberSliceCharts.Abelian.exists_fiber_slice_chart
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p) x₀ b e hb₀ hq hmap hproj
  let H : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AbelianFamilyPoints.FamilyPoints.fiber p s) ≃ₜ
      {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X // AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p x =
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p x₀} :=
    (AbelianFamilyPoints.FamilyPoints.fiberHomeomorph p s).trans (Homeomorph.setCongr (by
      ext x
      change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p x = s ↔
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p x = AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p x₀
      rw [hx₀]))
  have hH (q : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AbelianFamilyPoints.FamilyPoints.fiber p s)) :
      (H q).val = AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) q := rfl
  have hHi (y : {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X // AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p x =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p x₀}) :
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) (H.symm y) = y.val :=
    (hH (H.symm y)).symm.trans (congrArg Subtype.val (H.apply_symm_apply y))
  refine ⟨H.transOpenPartialHomeomorph c, hc, ?_, ?_, ?_⟩
  · change c.target = _
    simpa only [hx₀] using ht
  · intro q
    change c (H q) = _
    rw [hf, hH]
  · intro v hv
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) (H.symm (c.symm v)) = _
    rw [hHi, hi v hv, hx₀]

end

end OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberCharts.Abelian.FamilyPoints
