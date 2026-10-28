import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectivePresentation

/-! # Selected Section Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SelectedSectionEmbedding

noncomputable section

/-!
A proper section morphism is a closed immersion when a subfamily of its
charts covers the source and has surjective coordinate maps. Extra numerator
sections need not be assumed to have affine nonvanishing opens.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u v

variable {S X : Scheme.{u}} {L : X.Modules} {n : ℕ}

/-- Surjective evaluation on one affine nonvanishing open makes its chart map a closed immersion. -/
theorem sectionAffineChart_closedImmersion (f : X ⟶ S)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L)) (i : Fin (n + 1))
    (ha : IsAffineOpen (Ample.LineBundles.sectionNonvanishing (s i)))
    (hgen : Function.Surjective
      (ProjectiveChart.Evaluation.projectiveChartEvaluation ((Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ f).appTop.hom
        (fun k => Section.Frames.sectionRatio (s i) (s k)) i (Section.Frames.sectionRatio_self (s i)))) :
    IsClosedImmersion (Section.Embedding.sectionAffineChart f s i) := by
  have : IsAffine (Ample.LineBundles.sectionNonvanishing (s i)).toScheme := ha
  have hspec : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (ProjectiveChart.Evaluation.projectiveChartEvaluation ((Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ f).appTop.hom
        (fun k => Section.Frames.sectionRatio (s i) (s k)) i (Section.Frames.sectionRatio_self (s i))))) :=
    IsClosedImmersion.spec_of_surjective _ hgen
  have hto : IsClosedImmersion (Ample.LineBundles.sectionNonvanishing (s i)).toScheme.toSpecΓ := by
    infer_instance
  exact @IsClosedImmersion.comp _ _ _ _ _ hto hspec

/-- Generating ratios on a covering selection of affine charts give a preimmersion. -/
theorem sectionAbsoluteMorphism_preimmersion_of_selected (f : X ⟶ S)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    {ι : Type v} (j : ι → Fin (n + 1))
    (hcover : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s (j i)))
    (ha : ∀ i, IsAffineOpen (Ample.LineBundles.sectionNonvanishing (s (j i))))
    (hgen : ∀ i, Function.Surjective
      (ProjectiveChart.Evaluation.projectiveChartEvaluation ((Ample.LineBundles.sectionNonvanishing (s (j i))).ι ≫ f).appTop.hom
        (fun k => Section.Frames.sectionRatio (s (j i)) (s k)) (j i) (Section.Frames.sectionRatio_self (s (j i))))) :
    IsPreimmersion (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) := by
  let a := SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs
  have : MorphismProperty.RespectsRight (@IsPreimmersion) (@IsOpenImmersion) := ⟨by
    intro _ _ _ g hg f hf
    have : IsOpenImmersion g := hg
    have : IsPreimmersion f := hf
    infer_instance⟩
  have : MorphismProperty.HasOfPostcompProperty (@IsPreimmersion) (@IsOpenImmersion) := ⟨by
    intro _ _ _ f g hg hfg
    have : IsOpenImmersion g := hg
    have : IsPreimmersion (f ≫ g) := hfg
    exact IsPreimmersion.of_comp f g⟩
  apply IsZariskiLocalAtTarget.of_forall_source_exists_preimage (P := @IsPreimmersion) a
  intro x
  obtain ⟨i, hi⟩ := hcover x
  let V := Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n) (MvPolynomial.X (j i))
  have he : a ⁻¹ᵁ V = Ample.LineBundles.sectionNonvanishing (s (j i)) :=
    ProjectiveChart.Preimages.sectionAbsoluteMorphism_preimage f s hs (j i)
  refine ⟨V, (congrArg (fun U : X.Opens => x ∈ U) he).mpr hi, ?_⟩
  have hchart : IsClosedImmersion (Section.Embedding.sectionAffineChart f s (j i)) :=
    sectionAffineChart_closedImmersion f s (j i) (ha i) (hgen i)
  have hopen : IsOpenImmersion (Proj.awayι (Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n)
      (MvPolynomial.X (j i)) (MvPolynomial.isHomogeneous_X Γ(S, ⊤) (j i)) Nat.zero_lt_one) := by
    change IsOpenImmersion ((Proj.basicOpenIsoSpec (Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n)
      (MvPolynomial.X (j i)) (MvPolynomial.isHomogeneous_X Γ(S, ⊤) (j i)) Nat.zero_lt_one).inv ≫ V.ι)
    infer_instance
  have hpre : IsPreimmersion (Section.Embedding.sectionAffineChart f s (j i)) := inferInstance
  have hcomp : IsPreimmersion (Section.Embedding.sectionAffineChart f s (j i) ≫
      Proj.awayι (Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n) (MvPolynomial.X (j i))
        (MvPolynomial.isHomogeneous_X Γ(S, ⊤) (j i)) Nat.zero_lt_one) :=
    @IsPreimmersion.comp _ _ _ (Section.Embedding.sectionAffineChart f s (j i)) _ hpre inferInstance
  have habs : IsPreimmersion (Section.ChartOverlaps.sectionAbsoluteChart f s (j i)) :=
    (congrArg IsPreimmersion (Section.Embedding.sectionAffineChart_away f s (j i))).mp hcomp
  have hres : IsPreimmersion ((Ample.LineBundles.sectionNonvanishing (s (j i))).ι ≫ a) :=
    (congrArg IsPreimmersion (SectionsProjectiveMorphism.sectionAbsoluteMorphism_restrict f s hs (j i))).mpr habs
  exact (congrArg (fun U : X.Opens => IsPreimmersion (U.ι ≫ a)) he).mpr hres

/-- Properness closes the immersion supplied by the selected affine charts. -/
theorem sectionAbsoluteMorphism_closedImmersion_of_selected (f : X ⟶ S)
    [IsProper f] [IsAffine S]
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    {ι : Type v} (j : ι → Fin (n + 1))
    (hcover : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s (j i)))
    (ha : ∀ i, IsAffineOpen (Ample.LineBundles.sectionNonvanishing (s (j i))))
    (hgen : ∀ i, Function.Surjective
      (ProjectiveChart.Evaluation.projectiveChartEvaluation ((Ample.LineBundles.sectionNonvanishing (s (j i))).ι ≫ f).appTop.hom
        (fun k => Section.Frames.sectionRatio (s (j i)) (s k)) (j i) (Section.Frames.sectionRatio_self (s (j i))))) :
    IsClosedImmersion (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) := by
  have : IsPreimmersion (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) :=
    sectionAbsoluteMorphism_preimmersion_of_selected f s hs j hcover ha hgen
  have : IsProper (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) := Affine.SectionMorphism.sectionAbsoluteMorphism_proper f s hs
  apply IsClosedImmersion.of_isPreimmersion
  exact (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs).isClosedMap.isClosed_range

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SelectedSectionEmbedding
