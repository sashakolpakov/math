import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.LocalDescent
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SheafComplex

/-! # Sheaf Sections -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SheafSections

noncomputable section

/-! Sheafification preserves the actual holomorphic sections and their actual smooth inclusion. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem holomorphicComplexSheafificationUnit_isIso :
    IsIso ((SheafComplex.complexSheafificationAdjunction M).unit.app (Presheaf.presheafComplex E M)) := by
  have h (n : ℕ) : IsIso (((SheafComplex.complexSheafificationAdjunction M).unit.app (Presheaf.presheafComplex E M)).f n) :=
    CategoryTheory.isIso_toSheafify (Opens.grothendieckTopology M) (LocalDescent.holomorphicPresheaf_isSheaf E M n)
  exact HomologicalComplex.Hom.isIso_of_components _

def holomorphicSheafSectionIso (U : Opens M) (n : ℕ) :
    ModuleCat.of ℂ (DeRhamComplex.forms E U n) ≅ ((SheafComplex.sheafComplex E M).X n).obj.obj (op U) := by
  haveI := CategoryTheory.isIso_toSheafify (Opens.grothendieckTopology M)
    (LocalDescent.holomorphicPresheaf_isSheaf E M n)
  let e := asIso ((CategoryTheory.toSheafify (Opens.grothendieckTopology M)
    ((Presheaf.presheafComplex E M).X n)).app (op U))
  exact e

theorem holomorphicSheafSectionIso_inclusion (U : Opens M) (n : ℕ) (a : DeRhamComplex.forms E U n) :
    ((SheafComplex.inclusionSheafMap E M).f n).hom.app (op U) ((holomorphicSheafSectionIso E M U n).hom a) =
      LocalDescent.ambientHolomorphicInclusion U n a := by
  have h := congrArg (fun f => (f.f n).app (op U)) (SheafComplex.inclusionSheafMap_normalization E M)
  exact ConcreteCategory.congr_hom h a

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SheafSections
