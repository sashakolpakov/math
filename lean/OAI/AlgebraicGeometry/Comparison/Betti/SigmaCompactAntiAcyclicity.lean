import OAI.AlgebraicGeometry.Comparison.Betti.AntiFormSheafRetraction
import OAI.AlgebraicGeometry.Comparison.Betti.SigmaCompactSmoothAcyclicity
import OAI.AlgebraicGeometry.Comparison.Betti.ExtRetraction

/-! # Sigma Compact Anti Acyclicity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SigmaCompactAntiAcyclicity.Dolbeault

noncomputable section

/-! Every original pure antiholomorphic form sheaf on a sigma-compact
complex manifold is acyclic for the actual global-section Ext functor. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  [SigmaCompactSpace M] [T2Space M]

local instance : HasExt.{1} (ConstantSheafSections.ComplexSheaves (TopCat.of M)) := HasExt.standard _

theorem sigmaCompact_antiFormSheaf_ext_vanish (p q : ℕ) :
    Subsingleton (Ext.{1} (ConstantSheafSections.standardConstantSheaf (TopCat.of M))
      (DivisorClass.Chern.PureManifoldDolbeaultSheaf.antiOpenManifoldFormSheaf E M p) (q + 1)) := by
  have hs : Subsingleton (Ext.{1} (ConstantSheafSections.standardConstantSheaf (TopCat.of M))
      (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M p) (q + 1)) := SigmaCompactSmoothAcyclicity.Godement.sigmaCompact_smoothFormSheaf_ext_vanish E M p q
  exact ExtRetraction.ext_subsingleton_of_retraction
    (C := ConstantSheafSections.ComplexSheaves (TopCat.of M)) (ConstantSheafSections.standardConstantSheaf (TopCat.of M))
    (AntiFormSheafRetraction.Dolbeault.antiFormSheafInclusion E M p) (AntiFormSheafRetraction.Dolbeault.antiFormSheafRetraction E M p)
    (AntiFormSheafRetraction.Dolbeault.antiFormSheafInclusion_retraction E M p) (q + 1)

end

end OAI.AlgebraicGeometry.Comparison.Betti.SigmaCompactAntiAcyclicity.Dolbeault
