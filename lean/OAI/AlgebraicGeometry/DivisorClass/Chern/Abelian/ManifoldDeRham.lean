import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.SheafLocalExact
import OAI.Analysis.DifferentialForms.Manifold.ManifoldSheaf
import OAI.Analysis.DifferentialForms.Manifold.LocallyConstant
import OAI.Analysis.DifferentialForms.Manifold.LocalPoincare
import OAI.AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf

/-! # Manifold De Rham -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.ManifoldDeRham

noncomputable section

/-! Original manifold forms and their proved de Rham exactness as abelian sheaves. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def abelianLocallyConstantComplexSheaf (X : TopCat.{0}) : TopCat.Sheaf AddCommGrpCat.{0} X :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf X)

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def abelianManifoldFormSheaf (n : ℕ) : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M) :=
  (sheafCompose (Opens.grothendieckTopology (TopCat.of M))
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M n)

def abelianManifoldFormSheafD (n : ℕ) :
    abelianManifoldFormSheaf E M n ⟶ abelianManifoldFormSheaf E M (n + 1) :=
  ObjectProperty.homMk {
    app U := AddCommGrpCat.ofHom (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (E := E) (U := U.unop) (n := n)).toAddMonoidHom
    naturality := by
      intro U V i
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro a
      exact (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_d (leOfHom i.unop) a).symm }

theorem abelianManifoldFormSheafD_squared (n : ℕ) :
    abelianManifoldFormSheafD E M n ≫ abelianManifoldFormSheafD E M (n + 1) = 0 := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  exact Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d_squared a

def abelianManifoldLocallyConstantInclusion :
    abelianLocallyConstantComplexSheaf (TopCat.of M) ⟶ abelianManifoldFormSheaf E M 0 :=
  ObjectProperty.homMk {
    app U := AddCommGrpCat.ofHom (Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm E U.unop).toAddMonoidHom
    naturality := by
      intro U V i
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro f
      exact (Analysis.DifferentialForms.Manifold.LocallyConstant.restrict_locallyConstantToManifoldZeroForm (E := E) (leOfHom i.unop) f).symm }

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem abelianManifoldLocallyConstantInclusion_mono : Mono (abelianManifoldLocallyConstantInclusion E M) := by
  apply (CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono _ _ _).mpr
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro U
  exact (AddCommGrpCat.mono_iff_injective _).mpr (Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm_injective (E := E) U.unop)

theorem abelianManifoldLocallyConstantInclusion_d :
    abelianManifoldLocallyConstantInclusion E M ≫ abelianManifoldFormSheafD E M 0 = 0 := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro f
  exact Analysis.DifferentialForms.Manifold.LocallyConstant.d_locallyConstantToManifoldZeroForm (E := E) U.unop f

def abelianManifoldDeRhamZeroSequence : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M)) :=
  ShortComplex.mk (abelianManifoldLocallyConstantInclusion E M) (abelianManifoldFormSheafD E M 0)
    (abelianManifoldLocallyConstantInclusion_d E M)

theorem abelianManifoldDeRhamZeroSequence_exact : (abelianManifoldDeRhamZeroSequence E M).Exact := by
  apply SheafLocalExact.abelianSheaf_exact_of_section_exact (TopCat.of M)
  intro U
  rw [ShortComplex.ab_exact_iff]
  intro a ha
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a = 0 at ha
  have hr : a ∈ LinearMap.range (Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm E U) := by
    rw [Analysis.DifferentialForms.Manifold.LocallyConstant.range_locallyConstantToManifoldZeroForm]
    exact ha
  exact hr

def abelianManifoldDeRhamStep (n : ℕ) : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M)) :=
  ShortComplex.mk (abelianManifoldFormSheafD E M n) (abelianManifoldFormSheafD E M (n + 1))
    (abelianManifoldFormSheafD_squared E M n)

variable [FiniteDimensional ℝ E]

theorem abelianManifoldDeRhamStep_exact (n : ℕ) : (abelianManifoldDeRhamStep E M n).Exact := by
  apply SheafLocalExact.abelianSheaf_exact_of_local_lifts (TopCat.of M) (abelianManifoldDeRhamStep E M n)
  intro U a ha x hx
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a = 0 at ha
  obtain ⟨V, hVU, hxV, t, ht⟩ := Analysis.DifferentialForms.Manifold.LocalPoincare.manifold_local_poincare U a ha ⟨x, hx⟩
  exact ⟨V, hxV, hVU, t, ht⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.ManifoldDeRham
