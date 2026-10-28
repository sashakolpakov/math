import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.ProjectivePresentation

/-! # Ample Section Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AmpleSectionEmbedding

noncomputable section

/-! Retain the sections and positive tensor powers in the actual ample
embedding construction, for comparison with its Chern class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {X S : Scheme.{0}}

theorem section_cover_exists_power_embedding (L : HilbertConstruction.Line.Bundles.LineBundle X)
    [CompactSpace X] [X.IsSeparated] (f : X ⟶ S) [IsProper f] [IsAffine S] {k : ℕ}
    (s : Fin (k + 1) → (HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf))
    (hs : ∀ x : X, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (ha : ∀ i, IsAffineOpen (HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))) :
    ∃ (d : ℕ), 0 < d ∧ ∃ (n : ℕ)
      (q : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.tensorPower d).sheaf))
      (hq : ∀ x : X, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (q i)),
      IsClosedImmersion (HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f q hq) := by
  obtain ⟨d, hd, n, q, j, hq, hgen⟩ := L.generating_power_family f s ha
  have hD (i : Fin (k + 1)) : HilbertConstruction.Ample.LineBundles.sectionNonvanishing (q (j i)) = HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i) :=
    (congrArg HilbertConstruction.Ample.LineBundles.sectionNonvanishing (hq i)).trans (HilbertConstruction.Section.PowerLocus.sectionNonvanishing_tensorPowerSection (s i) d hd)
  have hcover : ∀ x : X, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (q (j i)) := by
    intro x
    obtain ⟨i, hi⟩ := hs x
    exact ⟨i, (congrArg (fun U : X.Opens => x ∈ U) (hD i)).mpr hi⟩
  have hsq : ∀ x : X, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (q i) := by
    intro x
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨j i, hi⟩
  have haq (i : Fin (k + 1)) : IsAffineOpen (HilbertConstruction.Ample.LineBundles.sectionNonvanishing (q (j i))) :=
    (congrArg IsAffineOpen (hD i)).mpr (ha i)
  exact ⟨d, hd, n, q, hsq,
    HilbertConstruction.SelectedSectionEmbedding.sectionAbsoluteMorphism_closedImmersion_of_selected f q hsq j hcover haq hgen⟩

theorem ample_exists_sections_embedding (L : HilbertConstruction.Line.Bundles.LineBundle X) (hL : L.IsAmple)
    (f : X ⟶ S) [IsProper f] [IsAffine S] :
    ∃ (d e : ℕ), 0 < d ∧ 0 < e ∧ ∃ (n : ℕ)
      (q : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule X ⟶ ((L.tensorPower d).tensorPower e).sheaf))
      (hq : ∀ x : X, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (q i)),
      IsClosedImmersion (HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f q hq) := by
  have : CompactSpace X := ⟨hL.1⟩
  have : X.IsSeparated := ⟨(terminal.comp_from f) ▸
    (inferInstance : IsSeparated (f ≫ terminal.from S))⟩
  obtain ⟨d, hd, k, s, hs, ha⟩ := hL.projective_section_family
  obtain ⟨e, he, n, q, hq, hc⟩ := section_cover_exists_power_embedding (L.tensorPower d) f s hs ha
  exact ⟨d, e, hd, he, n, q, hq, hc⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AmpleSectionEmbedding
