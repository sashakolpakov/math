import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.ProjectivePresentation

/-! # Projective Embeddings -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Projective embeddings with their positive tensor degree and actual generating sections retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}}

structure Power.ProjectiveEmbeddings.PowerProjectiveEmbedding (L : Line.Bundles.LineBundle X) (f : X ⟶ S) where
  degree : ℕ
  degree_pos : 0 < degree
  power : Line.Bundles.LineBundle X
  isPower : Tensor.Powers.IsTensorPower L.sheaf degree power.sheaf
  dimension : ℕ
  sections : Fin (dimension + 1) → (Line.Bundles.structureModule X ⟶ power.sheaf)
  covers : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (sections i)
  closedImmersion : IsClosedImmersion (SectionsProjectiveMorphism.sectionProjectiveMorphism f sections covers).left

theorem Power.ProjectiveEmbeddings.sectionProjectiveMorphism_closedImmersion_of_absolute (f : X ⟶ S) [IsAffine S]
    {M : X.Modules} {n : ℕ} (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ M))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (h : IsClosedImmersion (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)) :
    IsClosedImmersion (SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs).left := by
  let a := SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs
  let p : (Projective.ProjectivePresentations.projectiveSpaceOver S n).left ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).left :=
    Limits.pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ
  have hp : a.left ≫ p = SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs := Limits.pullback.lift_fst _ _ _
  have : IsClosedImmersion (a.left ≫ p) := hp.symm ▸ h
  have : IsIso p := inferInstanceAs
    (IsIso (Limits.pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ))
  exact IsClosedImmersion.of_comp a.left p

theorem Line.Bundles.LineBundle.IsAmple.exists_powerProjectiveEmbedding {L : Line.Bundles.LineBundle X} (hL : L.IsAmple)
    (f : X ⟶ S) [IsProper f] [IsAffine S] : Nonempty (Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L f) := by
  have : CompactSpace X := ⟨hL.1⟩
  have : X.IsSeparated := ⟨(Limits.terminal.comp_from f) ▸
    (inferInstance : IsSeparated (f ≫ Limits.terminal.from S))⟩
  obtain ⟨d, hd, k, s, hs, ha⟩ := hL.projective_section_family
  obtain ⟨m, hm, n, q, j, hq, hgen⟩ := (L.tensorPower d).generating_power_family f s ha
  have hD (i : Fin (k + 1)) : Ample.LineBundles.sectionNonvanishing (q (j i)) = Ample.LineBundles.sectionNonvanishing (s i) :=
    (congrArg Ample.LineBundles.sectionNonvanishing (hq i)).trans (Section.PowerLocus.sectionNonvanishing_tensorPowerSection (s i) m hm)
  have hcover : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (q (j i)) := by
    intro x
    obtain ⟨i, hi⟩ := hs x
    exact ⟨i, (congrArg (fun U : X.Opens => x ∈ U) (hD i)).mpr hi⟩
  have hqcover : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (q i) := by
    intro x
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨j i, hi⟩
  have haq (i : Fin (k + 1)) : IsAffineOpen (Ample.LineBundles.sectionNonvanishing (q (j i))) :=
    (congrArg IsAffineOpen (hD i)).mpr (ha i)
  exact ⟨⟨m * d, Nat.mul_pos hm hd, (L.tensorPower d).tensorPower m,
    (L.tensorPower_isTensorPower (m * d)).of_targetIso (L.tensorPowerComposeIso m d), n, q, hqcover,
    Power.ProjectiveEmbeddings.sectionProjectiveMorphism_closedImmersion_of_absolute f q hqcover
      (SelectedSectionEmbedding.sectionAbsoluteMorphism_closedImmersion_of_selected f q hqcover j hcover haq hgen)⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
