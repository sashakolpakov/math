import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.FactorizationChartGeneration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisSectionRatioSubring
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectivePresentation

/-! # Factorization Basis Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.FactorizationBasisEmbedding

noncomputable section

/-! A complete section basis with consecutive-power factorizations generates
all projective chart rings. If its section map is finite, it is a closed immersion. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
variable (p : X ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X) {n : ℕ}
variable (b : Module.Basis (Fin (n + 1)) K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj L.sheaf))
variable (hfactor : ∀ m : ℕ, 0 < m → Section.FactorizationSpans.SectionFactorizationSpan (Line.Bundles.structureModule X)
  (L.tensorPower m).sheaf (L.tensorPower (1 + m)).sheaf)

include hfactor in
theorem sectionBasisFamily_ratios_generate : Section.ProjectivePresentation.SectionRatiosGenerate p (BasisSectionGeneration.sectionBasisFamily p L.sheaf b) := by
  intro i
  let s := BasisSectionGeneration.sectionBasisFamily p L.sheaf b
  let U := Ample.LineBundles.sectionNonvanishing (s i)
  let := (U.ι ≫ p).appTop.hom.toAlgebra
  let C := Algebra.adjoin Γ(Spec (.of K), ⊤) (Set.range (fun j => Section.Frames.sectionRatio (s i) (s j)))
  have hc : ∀ c : K, Coefficient.ModulePresheaf.schemeCoefficientMap (U.ι ≫ p) c ∈ C.toSubring := by
    intro c
    exact C.algebraMap_mem ((Scheme.ΓSpecIso (.of K)).inv c)
  have hb : ∀ j, Section.Frames.sectionRatio (s i) (BasisSectionGeneration.sectionBasisFamily p L.sheaf b j) ∈ C.toSubring :=
    fun j => Algebra.subset_adjoin ⟨j, rfl⟩
  have hC : C.toSubring = ⊤ := FactorizationChartGeneration.sectionRatio_subring_eq_top_of_power_factorizations L (s i)
    C.toSubring (BasisSectionRatioSubring.sectionRatio_mem_of_basis p (s i) b C.toSubring hc hb) hfactor
  apply top_unique
  intro r _
  have h : r ∈ C.toSubring := by rw [hC]; trivial
  exact h

include hfactor in
theorem sectionBasisFamily_closedImmersion_of_finite
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (BasisSectionGeneration.sectionBasisFamily p L.sheaf b i))
    [IsFinite (SectionsProjectiveMorphism.sectionProjectiveMorphism p (BasisSectionGeneration.sectionBasisFamily p L.sheaf b) hs).left] :
    IsClosedImmersion (SectionsProjectiveMorphism.sectionProjectiveMorphism p (BasisSectionGeneration.sectionBasisFamily p L.sheaf b) hs).left := by
  let s := BasisSectionGeneration.sectionBasisFamily p L.sheaf b
  let a := SectionsProjectiveMorphism.sectionAbsoluteMorphism p s hs
  let q := pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(Spec (.of K), ⊤) n).hom (Spec (.of K)).toSpecΓ
  have : IsIso q := inferInstance
  have : IsFinite q := inferInstance
  have he : (SectionsProjectiveMorphism.sectionProjectiveMorphism p s hs).left ≫ q = a := pullback.lift_fst _ _ _
  have : IsFinite a := by rw [← he]; infer_instance
  have ha : ∀ i, IsAffineOpen (Ample.LineBundles.sectionNonvanishing (s i)) := by
    intro i
    have h := (StandardProjectiveCharts.standardProjectiveChart_isAffine Γ(Spec (.of K), ⊤) n i).preimage a
    erw [ProjectiveChart.Preimages.sectionAbsoluteMorphism_preimage] at h
    exact h
  exact Section.Embedding.sectionProjectiveMorphism_closedImmersion p s hs ha
    (sectionBasisFamily_ratios_generate p L b hfactor).surjective

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.FactorizationBasisEmbedding
