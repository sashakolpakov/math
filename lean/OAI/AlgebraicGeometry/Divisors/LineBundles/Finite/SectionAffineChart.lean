import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.RegularPrincipalSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.OpenChart

/-! # Section Affine Chart -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.SectionAffineChart.BundleCycles

noncomputable section

/-! Every analytic point of the actual finite parent image admits an affine base chart with nonempty full inverse-image source and a literal lift of the point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [IsIntegral N.left] [Smooth N.hom] (k : S ⟶ N) [IsFinite k.left]

omit [Smooth S.hom] [AlgebraicGeometry.IsIntegral N.left] [Smooth N.hom] in
theorem finiteParentPoint_exists_affine_chart (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)
    (hy : y ∈ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)))) :
    ∃ B : N.left.Opens, IsAffine (FiniteAffine.OpenChart.BundleCycles.finiteAffineBase B).left ∧ Nonempty B ∧
      Nonempty (k.left ⁻¹ᵁ B) ∧
      ∃ x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (FiniteAffine.OpenChart.BundleCycles.finiteAffineBase B), ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FiniteAffine.OpenChart.BundleCycles.finiteAffineBaseInclusion B) x = y := by
  obtain ⟨B, hB, hyB, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y))
  have hy' := hy
  rw [CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion_range, CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport_eq_image] at hy'
  obtain ⟨z, _, hz⟩ := hy'
  have hne : Nonempty (k.left ⁻¹ᵁ B) := ⟨⟨z, by
    change k.left z ∈ B
    exact hz.symm ▸ hyB⟩⟩
  have hmem : y ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FiniteAffine.OpenChart.BundleCycles.finiteAffineBaseInclusion B)) := by
    rw [FiniteAffine.OpenChart.BundleCycles.finiteAffineBaseInclusion_analytic_range]
    exact hyB
  obtain ⟨x, hx⟩ := hmem
  exact ⟨B, hB, ⟨⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y, hyB⟩⟩, hne, x, hx⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.SectionAffineChart.BundleCycles
