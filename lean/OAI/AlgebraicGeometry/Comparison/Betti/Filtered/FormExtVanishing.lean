import OAI.AlgebraicGeometry.Comparison.Betti.Filtered.SmoothRetraction
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.FormExtVanishing
import OAI.AlgebraicGeometry.Comparison.Betti.ExtRetraction

/-! # Form Ext Vanishing -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Filtered.FormExtVanishing.Hodge

noncomputable section

/-! Each term of the actual filtered smooth complex is acyclic for global
sections, by its proved retraction from the smooth form sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  [CompactSpace M] [T2Space M]

local instance : HasExt.{1} (ConstantSheafSections.ComplexSheaves (TopCat.of M)) := HasExt.standard _

theorem filteredFormSheaf_ext_vanish (n : ℕ) (r : ℤ) (q : ℕ) :
    Subsingleton (Ext.{1} (ConstantSheafSections.standardConstantSheaf (TopCat.of M))
      (SmoothComplex.Hodge.filteredFormSheaf E M n r) (q + 1)) := by
  have hs : Subsingleton (Ext.{1} (ConstantSheafSections.standardConstantSheaf (TopCat.of M))
      (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M n) (q + 1)) := Smooth.FormExtVanishing.Godement.smoothFormSheaf_ext_vanish E M n q
  exact ExtRetraction.ext_subsingleton_of_retraction
    (C := ConstantSheafSections.ComplexSheaves (TopCat.of M)) (ConstantSheafSections.standardConstantSheaf (TopCat.of M))
    (SmoothComplex.Hodge.filteredFormSheafInclusion E M n r) (SmoothRetraction.Hodge.filteredFormSheafRetraction E M n r)
    (SmoothRetraction.Hodge.filteredFormSheafInclusion_retraction E M n r) (q + 1)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Filtered.FormExtVanishing.Hodge
