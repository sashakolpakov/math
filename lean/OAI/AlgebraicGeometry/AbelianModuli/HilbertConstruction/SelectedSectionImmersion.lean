import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SelectedSectionEmbedding

/-! # Selected Section Immersion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SelectedSectionImmersion

noncomputable section

/-! Generating ratios on a covering selection of affine charts give an actual immersion in projective space. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u v
variable {S X : Scheme.{u}} {L : X.Modules} {n : ℕ}

theorem sectionAbsoluteMorphism_immersion_of_selected (f : X ⟶ S)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    {ι : Type v} (j : ι → Fin (n + 1))
    (hcover : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s (j i)))
    (ha : ∀ i, IsAffineOpen (Ample.LineBundles.sectionNonvanishing (s (j i))))
    (hgen : ∀ i, Function.Surjective
      (ProjectiveChart.Evaluation.projectiveChartEvaluation ((Ample.LineBundles.sectionNonvanishing (s (j i))).ι ≫ f).appTop.hom
        (fun k => Section.Frames.sectionRatio (s (j i)) (s k)) (j i) (Section.Frames.sectionRatio_self (s (j i))))) :
    IsImmersion (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) := by
  let a := SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs
  have : MorphismProperty.RespectsRight (@IsImmersion) (@IsOpenImmersion) := ⟨by
    intro _ _ _ g hg f hf
    have : IsOpenImmersion g := hg
    have : IsImmersion f := hf
    infer_instance⟩
  have : MorphismProperty.HasOfPostcompProperty (@IsImmersion) (@IsOpenImmersion) := ⟨by
    intro _ _ _ f g hg hfg
    have : IsOpenImmersion g := hg
    have : IsImmersion (f ≫ g) := hfg
    exact IsImmersion.of_comp f g⟩
  apply IsZariskiLocalAtTarget.of_forall_source_exists_preimage (P := @IsImmersion) a
  intro x
  obtain ⟨i, hi⟩ := hcover x
  let V := Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n) (MvPolynomial.X (j i))
  have he : a ⁻¹ᵁ V = Ample.LineBundles.sectionNonvanishing (s (j i)) :=
    ProjectiveChart.Preimages.sectionAbsoluteMorphism_preimage f s hs (j i)
  refine ⟨V, (congrArg (fun U : X.Opens => x ∈ U) he).mpr hi, ?_⟩
  have hchart : IsClosedImmersion (Section.Embedding.sectionAffineChart f s (j i)) :=
    SelectedSectionEmbedding.sectionAffineChart_closedImmersion f s (j i) (ha i) (hgen i)
  have hopen : IsOpenImmersion (Proj.awayι (Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n)
      (MvPolynomial.X (j i)) (MvPolynomial.isHomogeneous_X Γ(S, ⊤) (j i)) Nat.zero_lt_one) := by
    change IsOpenImmersion ((Proj.basicOpenIsoSpec (Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n)
      (MvPolynomial.X (j i)) (MvPolynomial.isHomogeneous_X Γ(S, ⊤) (j i)) Nat.zero_lt_one).inv ≫ V.ι)
    infer_instance
  have hpre : IsImmersion (Section.Embedding.sectionAffineChart f s (j i)) := inferInstance
  have hcomp : IsImmersion (Section.Embedding.sectionAffineChart f s (j i) ≫
      Proj.awayι (Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n) (MvPolynomial.X (j i))
        (MvPolynomial.isHomogeneous_X Γ(S, ⊤) (j i)) Nat.zero_lt_one) :=
    @IsImmersion.comp _ _ _ (Section.Embedding.sectionAffineChart f s (j i)) _ hpre inferInstance
  have habs : IsImmersion (Section.ChartOverlaps.sectionAbsoluteChart f s (j i)) :=
    (congrArg IsImmersion (Section.Embedding.sectionAffineChart_away f s (j i))).mp hcomp
  have hres : IsImmersion ((Ample.LineBundles.sectionNonvanishing (s (j i))).ι ≫ a) :=
    (congrArg IsImmersion (SectionsProjectiveMorphism.sectionAbsoluteMorphism_restrict f s hs (j i))).mpr habs
  exact (congrArg (fun U : X.Opens => IsImmersion (U.ι ≫ a)) he).mpr hres

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SelectedSectionImmersion
