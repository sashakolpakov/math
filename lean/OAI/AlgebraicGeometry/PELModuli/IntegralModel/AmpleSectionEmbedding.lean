import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.ProjectivePresentation

/-! # Ample Section Embedding -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmpleSectionEmbedding.PolarizationEmbedding

noncomputable section

/-! Retain the actual sections and their common positive tensor degree
when constructing a closed projective embedding from an ample bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (f : X ⟶ S)

/-- The projective embedding is given by specified sections of an actual
positive tensor power of the supplied ample bundle. -/
theorem exists_closed_section_embedding [IsProper f] [IsAffine S] (hL : L.IsAmple) :
    ∃ (d : ℕ), 0 < d ∧ ∃ (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X), AbelianModuli.HilbertConstruction.Tensor.Powers.IsTensorPower L.sheaf d P.sheaf ∧
      ∃ (n : ℕ) (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ P.sheaf))
        (hs : ∀ x : X, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)),
        IsClosedImmersion (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs).left := by
  have : CompactSpace X := ⟨hL.1⟩
  have : X.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from f]
    infer_instance⟩
  obtain ⟨a, ha, k, s, hs, hsa⟩ := hL.projective_section_family
  let Q := L.tensorPower a
  obtain ⟨b, hb, n, q, j, hq, hgen⟩ := Q.generating_power_family f s hsa
  have hD (i : Fin (k + 1)) : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (q (j i)) = AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i) :=
    (congrArg AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (hq i)).trans (AbelianModuli.HilbertConstruction.Section.PowerLocus.sectionNonvanishing_tensorPowerSection (s i) b hb)
  have hcover : ∀ x : X, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (q (j i)) := by
    intro x
    obtain ⟨i, hi⟩ := hs x
    exact ⟨i, (congrArg (fun U : X.Opens => x ∈ U) (hD i)).mpr hi⟩
  have hsq : ∀ x : X, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (q i) := by
    intro x
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨j i, hi⟩
  have haq (i : Fin (k + 1)) : IsAffineOpen (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (q (j i))) :=
    (congrArg IsAffineOpen (hD i)).mpr (hsa i)
  have habs : IsClosedImmersion (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f q hsq) :=
    AbelianModuli.HilbertConstruction.SelectedSectionEmbedding.sectionAbsoluteMorphism_closedImmersion_of_selected f q hsq j hcover haq hgen
  let p : (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S n).left ⟶ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).left :=
    CategoryTheory.Limits.pullback.fst (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ
  have hp : (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism f q hsq).left ≫ p = AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f q hsq :=
    CategoryTheory.Limits.pullback.lift_fst _ _ _
  have : IsClosedImmersion ((AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism f q hsq).left ≫ p) := hp.symm ▸ habs
  have : IsIso p := inferInstanceAs
    (IsIso (CategoryTheory.Limits.pullback.fst (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ))
  exact ⟨b * a, Nat.mul_pos hb ha, Q.tensorPower b,
    (L.tensorPower_isTensorPower (b * a)).of_targetIso (L.tensorPowerComposeIso b a),
    n, q, hsq, IsClosedImmersion.of_comp (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism f q hsq).left p⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmpleSectionEmbedding.PolarizationEmbedding
