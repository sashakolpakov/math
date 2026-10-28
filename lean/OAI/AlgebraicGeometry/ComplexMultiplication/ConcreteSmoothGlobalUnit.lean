import OAI.AlgebraicGeometry.ComplexMultiplication.SmoothIntegrationGlobalValues
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSections

/-! # Concrete Smooth Global Unit -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ConcreteSmoothGlobalUnit

noncomputable section

/-! # Actual smooth global cochains and sheafification retain simplex integration -/

open _root_.CategoryTheory _root_.TopologicalSpace OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSections
open scoped _root_.Manifold ContDiff

variable (Model M : Type) [NormedAddCommGroup Model] [NormedSpace ℝ Model]
  [TopologicalSpace M] [ChartedSpace Model M]

local notation "J" => Opens.grothendieckTopology (TopCat.of M)
local notation "A" => ModuleCat.of ℂ ℂ
local notation "P" => OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex Model M A
/-- Evaluate small complex-module sheaves on the actual top open. -/
abbrev actualSmoothGlobalSectionsFunctor :
    TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of M) ⥤ ModuleCat.{0} ℂ :=
  Analysis.DifferentialForms.Manifold.SheafDeRham.complexModuleSheafSections (⊤ : Opens M)

instance actualSmoothGlobalSectionsFunctor_preservesZeroMorphisms :
    (actualSmoothGlobalSectionsFunctor M).PreservesZeroMorphisms where
  map_zero _ _ := rfl

local notation "Γ" => OAI.AlgebraicGeometry.ComplexMultiplication.ConcreteSmoothGlobalUnit.actualSmoothGlobalSectionsFunctor M

/-- Genuine global sections of the actual sheafified smooth-singular complex. -/
def actualSmoothSingularGlobalComplex : CochainComplex (ModuleCat ℂ) ℕ :=
  (Functor.mapHomologicalComplex (Γ) (ComplexShape.up ℕ)).obj
    (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex Model M A)

/-- The canonical sheafification unit on actual top-open cochains. -/
def actualSmoothPresheafToGlobalSheafSections :
    AlgebraicTopology.DeRham.Comparison.CechComplexAugmentation.presheafComplexSections (⊤ : Opens M) (P) ⟶
      actualSmoothSingularGlobalComplex Model M where
  f n := (toSheafify J ((P).X n)).app (Opposite.op ⊤)
  comm' p q _ := by
    exact (congrArg (fun f => f.app (Opposite.op ⊤))
      (toSheafify_naturality J ((P).d p q))).symm

/-- Ambient smooth cochains enter actual global sheaf sections by the same unit. -/
def actualSmoothCochainsToGlobalSheafSections :
    AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains Model A M ⟶ actualSmoothSingularGlobalComplex Model M :=
  (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSections.manifoldSmoothPresheafTopIso Model M A).inv ≫
    actualSmoothPresheafToGlobalSheafSections Model M

/-- Each component is literal restriction to the top open followed by sheafification. -/
theorem actualSmoothCochainsToGlobalSheafSections_f (n : ℕ) :
    (actualSmoothCochainsToGlobalSheafSections Model M).f n =
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothPullback Model Model A
        (Subtype.val : (⊤ : Opens M) → M)
          (contMDiff_subtype_val (I := 𝓘(ℝ, Model)) (n := ∞))).f n ≫
            (toSheafify J ((P).X n)).app (Opposite.op ⊤) := by
  rw [actualSmoothCochainsToGlobalSheafSections, HomologicalComplex.comp_f,
    AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSections.manifoldSmoothPresheafTopIso_inv]
  rfl

variable [IsManifold 𝓘(ℝ, Model) ∞ M]

/-- Taking genuine global sections of the actual sheaf integration map. -/
def actualSmoothGlobalSheafIntegration :
    Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafSectionsComplex Model (⊤ : Opens M) ⟶
      actualSmoothSingularGlobalComplex Model M :=
  (Functor.mapHomologicalComplex (Γ) (ComplexShape.up ℕ)).map
    (SmoothIntegrationGlobalValues.actualSmoothIntegrationSheaf Model M)

/-- The full global comparison square uses actual smooth-simplex integrals. -/
theorem actualSmoothGlobalIntegration_square :
    (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamGlobalSectionsIso Model M).inv ≫
        actualSmoothGlobalSheafIntegration Model M =
      AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap Model M ≫
        actualSmoothCochainsToGlobalSheafSections Model M := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply,
    actualSmoothCochainsToGlobalSheafSections_f]
  exact SmoothIntegrationGlobalValues.actualSmoothIntegrationSheaf_globalValues Model M n form

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ConcreteSmoothGlobalUnit
