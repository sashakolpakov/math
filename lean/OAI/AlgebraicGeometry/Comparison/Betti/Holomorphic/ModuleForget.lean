import OAI.AlgebraicGeometry.Comparison.Betti.ManifoldHolomorphicModuleSheaf
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SheafSections

/-! # Module Forget -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ModuleForget

noncomputable section

/-! Forgetting the holomorphic coefficient action recovers the original
holomorphic form sheaf, with the original sheafification and smooth inclusion. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

def holomorphicModuleSheafForgetIso (n : ℕ) :
    (SheafOfModules.toSheaf.{0} (ManifoldHolomorphicModuleSheaf.manifoldHolomorphicStructureSheaf E M)).obj
        (ManifoldHolomorphicModuleSheaf.manifoldHolomorphicFormModuleSheaf E M n) ≅
      (sheafCompose (Opens.grothendieckTopology M)
        (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj ((SheafComplex.sheafComplex E M).X n) := by
  have := CategoryTheory.isIso_toSheafify (Opens.grothendieckTopology M)
    (LocalDescent.holomorphicPresheaf_isSheaf E M n)
  let e := asIso (CategoryTheory.toSheafify (Opens.grothendieckTopology M)
    ((Presheaf.presheafComplex E M).X n))
  exact (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology M) AddCommGrpCat).preimageIso
    (Functor.isoWhiskerRight e (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}))

theorem holomorphicModuleSheafForgetIso_apply (U : Opens M) (n : ℕ)
    (a : DeRhamComplex.forms E U n) :
    (holomorphicModuleSheafForgetIso E M n).hom.hom.app (op U) a =
      (SheafSections.holomorphicSheafSectionIso E M U n).hom a := rfl

theorem holomorphicModuleSheafForgetIso_inclusion (U : Opens M) (n : ℕ)
    (a : DeRhamComplex.forms E U n) :
    ((SheafComplex.inclusionSheafMap E M).f n).hom.app (op U)
        ((holomorphicModuleSheafForgetIso E M n).hom.hom.app (op U) a) =
      LocalDescent.ambientHolomorphicInclusion U n a :=
  SheafSections.holomorphicSheafSectionIso_inclusion E M U n a

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ModuleForget
