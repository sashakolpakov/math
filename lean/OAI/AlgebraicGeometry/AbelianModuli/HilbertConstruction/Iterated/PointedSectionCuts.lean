import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedSectionComponentCuts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReducedClosedSubschemes
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.ZeroDimensionalFinite

/-! # Pointed Section Cuts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.PointedSectionCuts

noncomputable section

/-! Repeated sections through a fixed rational point reduce a
dimension-d scheme mapping quasi-finitely to the ambient scheme to a
finite common zero set after exactly d cuts. Reduced closed subschemes
are used only to carry the intermediate underlying closed sets. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u
variable {K : Type u} [Field K] [Infinite K] {X : Scheme.{u}}

def reducedClosedSubschemeHomeomorph (Y : Scheme.{u}) (C : Closeds Y) :
    ReducedClosedSubschemes.reducedClosedSubscheme Y C ≃ₜ (C : Set Y) :=
  (IsClosedImmersion.isClosedEmbedding (ReducedClosedSubschemes.reducedClosedInclusion Y C)).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (ReducedClosedSubschemes.reducedClosedInclusion_range Y C))

theorem exists_pointed_sections_with_finite_common_zeros
    (p : X ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X) {n : ℕ}
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hcover : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ha : ∀ i, IsAffineOpen (Ample.LineBundles.sectionNonvanishing (s i)))
    (hgen : Section.ProjectivePresentation.SectionRatiosGenerate p s)
    (z : Spec (.of K) ⟶ X) (hz : z ≫ p = 𝟙 _) (d : ℕ) :
    ∀ (Y : Scheme.{u}) [NoetherianSpace Y]
      (f : Y ⟶ X) [LocallyQuasiFinite f],
      topologicalKrullDim Y ≤ d →
      ∃ ts : List (Line.Bundles.structureModule X ⟶ L.sheaf),
        ts.length = d ∧
        (∀ t ∈ ts, z (IsLocalRing.closedPoint K) ∉ Ample.LineBundles.sectionNonvanishing t) ∧
        {y : Y | ∀ t ∈ ts, f y ∉ Ample.LineBundles.sectionNonvanishing t}.Finite := by
  induction d with
  | zero =>
    intro Y _ f _ hdim
    let : Finite Y := Noetherian.ZeroDimensionalFinite.finite_of_noetherian_topologicalKrullDim_nonpos Y hdim
    exact ⟨[], rfl, by simp, Set.toFinite _⟩
  | succ d ih =>
    intro Y _ f _ hdim
    obtain ⟨t, htz, ht⟩ := PointedSectionComponentCuts.exists_pointed_section_dropping_dimension
      p L s hcover ha hgen z hz f d hdim
    let C : Closeds Y := ⟨{y : Y | f y ∉ Ample.LineBundles.sectionNonvanishing t},
      ((Ample.LineBundles.sectionNonvanishing t).isOpen.preimage f.continuous).isClosed_compl⟩
    let V := ReducedClosedSubschemes.reducedClosedSubscheme Y C
    let j := ReducedClosedSubschemes.reducedClosedInclusion Y C
    let : NoetherianSpace V :=
      (IsClosedImmersion.isClosedEmbedding j).isEmbedding.isInducing.noetherianSpace
    let : LocallyQuasiFinite (j ≫ f) := inferInstance
    have hdimV : topologicalKrullDim V ≤ d :=
      (reducedClosedSubschemeHomeomorph Y C).isInducing.topologicalKrullDim_le.trans ht
    obtain ⟨ts, hlen, hzts, hfinite⟩ := ih V (j ≫ f) hdimV
    refine ⟨t :: ts, by simp only [List.length_cons, hlen], ?_, ?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact htz
      · exact hzts a ha
    · apply (hfinite.image j).subset
      intro y hy
      have hyC : y ∈ (C : Set Y) := hy t (by simp)
      have hyrange : y ∈ Set.range j := by
        rw [show Set.range j = (C : Set Y) from ReducedClosedSubschemes.reducedClosedInclusion_range Y C]
        exact hyC
      obtain ⟨w, hw⟩ := hyrange
      refine ⟨w, ?_, hw⟩
      intro a ha
      change f (j w) ∉ Ample.LineBundles.sectionNonvanishing a
      rw [hw]
      exact hy a (List.mem_cons_of_mem _ ha)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.PointedSectionCuts
