import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.RingSectionBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.FactorizationChartGeneration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectivePresentation

/-! # Base Basis Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BaseBasisEmbedding

noncomputable section

/-! Over an affine base, a complete basis and consecutive-power section
factorizations turn a finite section morphism into a closed immersion. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S X : Scheme.{u}} [IsAffine S] [CompactSpace X] [X.IsSeparated]
variable (f : X ⟶ S) (L : Line.Bundles.LineBundle X) {n : ℕ}
variable (b : Module.Basis (Fin (n + 1)) Γ(S, ⊤)
  ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor f.appTop.hom).obj L.sheaf))
variable (hfactor : ∀ m : ℕ, 0 < m → Section.FactorizationSpans.SectionFactorizationSpan (Line.Bundles.structureModule X)
  (L.tensorPower m).sheaf (L.tensorPower (1 + m)).sheaf)

include hfactor in
omit [IsAffine S] in
theorem coefficientRingBasisFamily_ratios_generate :
    Section.ProjectivePresentation.SectionRatiosGenerate f (Coefficient.RingSectionBasis.coefficientRingBasisFamily f.appTop.hom L.sheaf b) := by
  intro i
  let s := Coefficient.RingSectionBasis.coefficientRingBasisFamily f.appTop.hom L.sheaf b
  let U := Ample.LineBundles.sectionNonvanishing (s i)
  let := (U.ι ≫ f).appTop.hom.toAlgebra
  let C := Algebra.adjoin Γ(S, ⊤) (Set.range (fun j => Section.Frames.sectionRatio (s i) (s j)))
  have hc : ∀ r : Γ(S, ⊤), U.ι.appTop (f.appTop r) ∈ C.toSubring := fun r => C.algebraMap_mem r
  have hb : ∀ j, Section.Frames.sectionRatio (s i) (Coefficient.RingSectionBasis.coefficientRingBasisFamily f.appTop.hom L.sheaf b j) ∈
      C.toSubring := fun j => Algebra.subset_adjoin ⟨j, rfl⟩
  have hC : C.toSubring = ⊤ := Power.FactorizationChartGeneration.sectionRatio_subring_eq_top_of_power_factorizations L (s i)
    C.toSubring (Coefficient.RingSectionBasis.sectionRatio_mem_of_coefficientRing_basis f.appTop.hom (s i) b C.toSubring hc hb) hfactor
  apply top_unique
  intro r _
  have h : r ∈ C.toSubring := by rw [hC]; trivial
  exact h

include hfactor in
theorem coefficientRingBasisFamily_closedImmersion_of_finite
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (Coefficient.RingSectionBasis.coefficientRingBasisFamily f.appTop.hom L.sheaf b i))
    [IsFinite (SectionsProjectiveMorphism.sectionProjectiveMorphism f (Coefficient.RingSectionBasis.coefficientRingBasisFamily f.appTop.hom L.sheaf b) hs).left] :
    IsClosedImmersion (SectionsProjectiveMorphism.sectionProjectiveMorphism f (Coefficient.RingSectionBasis.coefficientRingBasisFamily f.appTop.hom L.sheaf b) hs).left := by
  let s := Coefficient.RingSectionBasis.coefficientRingBasisFamily f.appTop.hom L.sheaf b
  let a := SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs
  let q := pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ
  have : IsIso q := inferInstance
  have : IsFinite q := inferInstance
  have he : (SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs).left ≫ q = a := pullback.lift_fst _ _ _
  have : IsFinite a := by rw [← he]; infer_instance
  have ha : ∀ i, IsAffineOpen (Ample.LineBundles.sectionNonvanishing (s i)) := by
    intro i
    have h := (StandardProjectiveCharts.standardProjectiveChart_isAffine Γ(S, ⊤) n i).preimage a
    erw [ProjectiveChart.Preimages.sectionAbsoluteMorphism_preimage] at h
    exact h
  exact Section.Embedding.sectionProjectiveMorphism_closedImmersion f s hs ha
    (coefficientRingBasisFamily_ratios_generate f L b hfactor).surjective

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BaseBasisEmbedding
