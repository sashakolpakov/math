import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coproduct
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormsAffineLocality
import OAI.RepresentationTheory.Theta.Geometric.Geometry

/-! # Component Form Faithfulness -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! The original complex component restrictions jointly detect algebraic
one-forms, by the actual IntegralModel coproduct decomposition and base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormsAffineLocality

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.componentComplexInclusion_open (hg : D.pel.HasIntegralModelGeometry)
    (j : Fin D.pel.componentCount) :
    IsOpenImmersion (D.componentComplexInclusion j).left := by
  have : IsIso D.pel.componentAssembly := hg.decomposition
  have hi : Sigma.ι D.pel.components.S j ≫ (asIso D.pel.componentAssembly).hom =
      D.pel.inclusion j := by
    simp only [asIso_hom, AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.componentAssembly, Sigma.ι_comp_desc]
  have : IsOpenImmersion (D.pel.inclusion j).left :=
    hi ▸ AlgebraicGeometry.PELModuli.IntegralModel.Coproduct.decomposition_inclusion_open D.pel.components.S (asIso D.pel.componentAssembly) j
  have : IsOpenImmersion (D.pel.componentInclusion j).left :=
    AlgebraicGeometry.PELModuli.IntegralModel.Coproduct.baseChange_inclusion_open D.pel.generic (D.pel.inclusion j)
  exact AlgebraicGeometry.PELModuli.IntegralModel.Coproduct.baseChange_inclusion_open D.pel.complexGenericPoint (D.pel.componentInclusion j)

theorem Data.ActiveHeckeThetaData.componentComplexInclusion_cover (hg : D.pel.HasIntegralModelGeometry)
    (x : D.pel.complexSpace.left) :
    ∃ j, x ∈ Set.range (D.componentComplexInclusion j).left := by
  have : IsIso D.pel.componentAssembly := hg.decomposition
  have hi (j : Fin D.pel.componentCount) : Sigma.ι D.pel.components.S j ≫
      (asIso D.pel.componentAssembly).hom = D.pel.inclusion j := by
    simp only [asIso_hom, AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.componentAssembly, Sigma.ι_comp_desc]
  obtain ⟨j, hj⟩ := AlgebraicGeometry.PELModuli.IntegralModel.Coproduct.baseChange_decomposition_cover D.pel.components.S D.pel.generic
    (asIso D.pel.componentAssembly) (pullback.fst D.pel.space.hom D.pel.complexGenericPoint x)
  simp only [hi] at hj
  refine ⟨j, ?_⟩
  rw [Data.ActiveHeckeThetaData.componentComplexInclusion, AlgebraicGeometry.PELModuli.IntegralModel.Coproduct.baseChange_map_range]
  exact hj

theorem Data.ActiveHeckeThetaData.componentForms_jointly_injective (hg : D.pel.HasIntegralModelGeometry)
    (form other : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms D.pel.complexSpace)
    (h : ∀ j, AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (D.componentComplexInclusion j) form =
      AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (D.componentComplexInclusion j) other) : form = other :=
  AlgebraicGeometry.AbelianScheme.TateComparison.FormsAffineLocality.formsPullback_openCover_injective D.componentComplex D.componentComplexInclusion
    (D.componentComplexInclusion_open hg) (D.componentComplexInclusion_cover hg) form other h

end

/-! Every original complex moduli point lifts to an actual component
through its given open component inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.exists_component_complex_point (hg : D.pel.HasIntegralModelGeometry)
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace) :
    ∃ j : Fin D.pel.componentCount, ∃ x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (D.componentComplex j),
      x ≫ D.componentComplexInclusion j = p := by
  obtain ⟨j, hj⟩ := D.componentComplexInclusion_cover hg (p.left (IsLocalRing.closedPoint ℂ))
  let i := D.componentComplexInclusion j
  let : IsOpenImmersion i.left := D.componentComplexInclusion_open hg j
  let : Subsingleton (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)).left := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  have hsub : Set.range p.left ⊆ Set.range i.left := by
    rintro _ ⟨t, rfl⟩
    simpa only [Subsingleton.elim t (IsLocalRing.closedPoint ℂ)] using hj
  let l := IsOpenImmersion.lift i.left p.left hsub
  have hl : l ≫ i.left = p.left := IsOpenImmersion.lift_fac _ _ _
  let x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (D.componentComplex j) := Over.homMk l (by
    rw [← i.w, ← Category.assoc, hl]
    exact p.w)
  exact ⟨j, x, Over.OverMorphism.ext hl⟩

end

end OAI.RepresentationTheory.Theta.Geometric
