import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.ManifoldDeRham
import OAI.AlgebraicGeometry.DivisorClass.Chern.SecondQuotientCocycles
import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.TwoStepBoundary

/-! # De Rham Second Quotient -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DeRhamSecondQuotient

noncomputable section

/-! Actual degree-two de Rham connecting classes in ordinary coefficient-sheaf cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def manifoldDeRhamSecondQuotient : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M) :=
  cokernel (TwoStepQuotient.firstQuotientDifferential (Abelian.ManifoldDeRham.abelianManifoldDeRhamZeroSequence E M))

def manifoldDeRhamSecondQuotientInclusion :
    manifoldDeRhamSecondQuotient E M ⟶ Abelian.ManifoldDeRham.abelianManifoldFormSheaf E M 2 :=
  TwoStepQuotient.secondQuotientDifferential (Abelian.ManifoldDeRham.abelianManifoldDeRhamZeroSequence E M)
    (Abelian.ManifoldDeRham.abelianManifoldFormSheafD E M 1) (Abelian.ManifoldDeRham.abelianManifoldFormSheafD_squared E M 0)

def manifoldDeRhamConnectingClass :
    (manifoldDeRhamSecondQuotient E M).obj.obj (op (⊤ : Opens M)) →+
      CategoryTheory.Sheaf.H (Abelian.ManifoldDeRham.abelianLocallyConstantComplexSheaf (TopCat.of M)) 2 := by
  have : Mono (Abelian.ManifoldDeRham.abelianManifoldDeRhamZeroSequence E M).f := Abelian.ManifoldDeRham.abelianManifoldLocallyConstantInclusion_mono E M
  exact Chern.Sheaf.TwoStepBoundary.sheafTwoStepBoundary (Abelian.ManifoldDeRham.abelianManifoldDeRhamZeroSequence E M) (Abelian.ManifoldDeRham.abelianManifoldDeRhamZeroSequence_exact E M)

variable [FiniteDimensional ℝ E]

theorem manifoldDeRhamSecondQuotientInclusion_mono : Mono (manifoldDeRhamSecondQuotientInclusion E M) :=
  TwoStepQuotient.secondQuotientDifferential_mono (Abelian.ManifoldDeRham.abelianManifoldDeRhamZeroSequence E M)
    (Abelian.ManifoldDeRham.abelianManifoldFormSheafD E M 1) (Abelian.ManifoldDeRham.abelianManifoldFormSheafD_squared E M 0)
    (Abelian.ManifoldDeRham.abelianManifoldDeRhamStep_exact E M 0)

theorem manifoldDeRhamSecondQuotient_exists_lift (form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (⊤ : Opens M) 2)
    (hform : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d form = 0) :
    ∃ s : (manifoldDeRhamSecondQuotient E M).obj.obj (op (⊤ : Opens M)),
      (manifoldDeRhamSecondQuotientInclusion E M).hom.app (op (⊤ : Opens M)) s = form :=
  SecondQuotientCocycles.sheafSecondQuotient_exists_section (Abelian.ManifoldDeRham.abelianManifoldDeRhamZeroSequence E M)
    (Abelian.ManifoldDeRham.abelianManifoldFormSheafD E M 1) (Abelian.ManifoldDeRham.abelianManifoldFormSheafD_squared E M 0)
    (Abelian.ManifoldDeRham.abelianManifoldFormSheafD E M 2) (Abelian.ManifoldDeRham.abelianManifoldFormSheafD_squared E M 1)
    (Abelian.ManifoldDeRham.abelianManifoldDeRhamStep_exact E M 0) (Abelian.ManifoldDeRham.abelianManifoldDeRhamStep_exact E M 1) ⊤ form hform

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DeRhamSecondQuotient
