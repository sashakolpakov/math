import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothGlobalSheafification
import OAI.AlgebraicGeometry.DivisorClass.Chern.IntegratedHodgeSheaf

/-! # Global Integration Sheafification -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.GlobalIntegrationSheafification

noncomputable section

/-! The actual global integration map agrees with the integrated sheaf section used in Hodge vanishing. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem manifoldGlobalIntegration_sheaf_section (n : ℕ) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    ((Abelian.ManifoldIntegration.abelianManifoldIntegration E M).f n).hom.app (op (⊤ : Opens M)) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ form) =
      (SmoothGlobalSheafification.manifoldSmoothToAbelianSections E M).f n ((AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M).f n form) := by
  have h := ConcreteCategory.congr_hom (C := ModuleCat.{0} ℂ)
    (congrArg (fun f => f.f n) (AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegration_onOpen E (⊤ : Opens M))) form
  exact congrArg (fun c => (CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of M))
    ((AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ)).X n)).app (op (⊤ : Opens M)) c) h

theorem manifoldIntegratedSection_global (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 2) :
    IntegratedHodgeSheaf.manifoldIntegratedSection E M (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ form) =
      (SmoothGlobalSheafification.manifoldSmoothToAbelianSections E M).f 2 ((AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M).f 2 form) :=
  manifoldGlobalIntegration_sheaf_section E M 2 form

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.GlobalIntegrationSheafification
