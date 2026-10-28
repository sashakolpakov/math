import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.PresheafInclusion
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Adjunction
import OAI.AlgebraicGeometry.Comparison.Betti.MapCochainOf
import Mathlib.Topology.Sheaves.Abelian

/-! # Sheaf Complex -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SheafComplex

noncomputable section

/-! Sheafification of the independently defined holomorphic complex and its actual smooth inclusion. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

abbrev sheafCategory := Sheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)

def sheafComplex : CochainComplex (sheafCategory M) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)).mapHomologicalComplex
    (.up ℕ)).obj (Presheaf.presheafComplex E M)

def complexSheafificationAdjunction :
    (presheafToSheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)).mapHomologicalComplex (.up ℕ) ⊣
      (sheafToPresheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)).mapHomologicalComplex (.up ℕ) :=
  Complex.Adjunction.onComplexes
    (sheafificationAdjunction (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)) (.up ℕ)

def smoothSheafUnderlyingIso :
    ((sheafToPresheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)).mapHomologicalComplex
      (.up ℕ)).obj (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M) ≅ Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex E M :=
  MapCochainOf.Complex.mapCochainOfIso
    (sheafToPresheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ))
    (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M) (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheafD E M) (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheafD_squared E M)

def inclusionSheafMap : sheafComplex E M ⟶ Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M :=
  ((complexSheafificationAdjunction M).homEquiv (Presheaf.presheafComplex E M)
    (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M)).symm
      (PresheafInclusion.inclusionPresheafCochainMap E M ≫ (smoothSheafUnderlyingIso E M).inv)

theorem inclusionSheafMap_normalization :
    (complexSheafificationAdjunction M).unit.app (Presheaf.presheafComplex E M) ≫
        ((sheafToPresheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)).mapHomologicalComplex
          (.up ℕ)).map (inclusionSheafMap E M) =
      PresheafInclusion.inclusionPresheafCochainMap E M ≫ (smoothSheafUnderlyingIso E M).inv :=
  (complexSheafificationAdjunction M).homEquiv (Presheaf.presheafComplex E M)
    (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M) |>.apply_symm_apply _

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SheafComplex
