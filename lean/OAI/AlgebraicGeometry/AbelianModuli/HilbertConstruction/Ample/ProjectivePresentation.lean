import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GeneratingPowerFamily
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SelectedSectionEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.FiniteMorphism

/-! # Projective Presentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-!
A proper scheme over an affine base with an ample line bundle admits an
actual closed immersion into projective space over that base.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}}

/-- An affine nonvanishing cover from one line bundle on a proper scheme
over an affine base produces a projective presentation. -/
theorem Line.Bundles.LineBundle.projectivePresentation_of_section_cover (L : Line.Bundles.LineBundle X)
    [CompactSpace X] [X.IsSeparated] (f : X ⟶ S) [IsProper f] [IsAffine S] {k : ℕ}
    (s : Fin (k + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ha : ∀ i, IsAffineOpen (Ample.LineBundles.sectionNonvanishing (s i))) :
    Nonempty (Projective.ProjectivePresentations.ProjectivePresentation (Over.mk f)) := by
  obtain ⟨d, hd, n, q, j, hq, hgen⟩ := L.generating_power_family f s ha
  have hD (i : Fin (k + 1)) : Ample.LineBundles.sectionNonvanishing (q (j i)) = Ample.LineBundles.sectionNonvanishing (s i) :=
    (congrArg Ample.LineBundles.sectionNonvanishing (hq i)).trans (Section.PowerLocus.sectionNonvanishing_tensorPowerSection (s i) d hd)
  have hcover : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (q (j i)) := by
    intro x
    obtain ⟨i, hi⟩ := hs x
    exact ⟨i, (congrArg (fun U : X.Opens => x ∈ U) (hD i)).mpr hi⟩
  have hsq : ∀ x : X, ∃ l, x ∈ Ample.LineBundles.sectionNonvanishing (q l) := by
    intro x
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨j i, hi⟩
  have haq (i : Fin (k + 1)) : IsAffineOpen (Ample.LineBundles.sectionNonvanishing (q (j i))) :=
    (congrArg IsAffineOpen (hD i)).mpr (ha i)
  have habs : IsClosedImmersion (SectionsProjectiveMorphism.sectionAbsoluteMorphism f q hsq) :=
    SelectedSectionEmbedding.sectionAbsoluteMorphism_closedImmersion_of_selected f q hsq j hcover haq hgen
  let a := SectionsProjectiveMorphism.sectionProjectiveMorphism f q hsq
  let p : (Projective.ProjectivePresentations.projectiveSpaceOver S n).left ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).left :=
    pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ
  have hp : a.left ≫ p = SectionsProjectiveMorphism.sectionAbsoluteMorphism f q hsq := pullback.lift_fst _ _ _
  have : IsClosedImmersion (a.left ≫ p) := hp.symm ▸ habs
  have : IsIso p := inferInstanceAs
    (IsIso (pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ))
  exact ⟨⟨n, a, IsClosedImmersion.of_comp a.left p⟩⟩

/-- Ampleness on a proper scheme over an affine base gives a closed immersion
into a finite-dimensional projective space over the same base. -/
theorem Line.Bundles.LineBundle.IsAmple.exists_projectivePresentation {L : Line.Bundles.LineBundle X}
    (hL : L.IsAmple) (f : X ⟶ S) [IsProper f] [IsAffine S] :
    Nonempty (Projective.ProjectivePresentations.ProjectivePresentation (Over.mk f)) := by
  have : CompactSpace X := ⟨hL.1⟩
  have : X.IsSeparated := ⟨(terminal.comp_from f) ▸
    (inferInstance : IsSeparated (f ≫ terminal.from S))⟩
  obtain ⟨d, _hd, k, s, hs, ha⟩ := hL.projective_section_family
  exact (L.tensorPower d).projectivePresentation_of_section_cover f s hs ha

/-- The chosen actual projective presentation supplied by an ample line bundle. -/
def Line.Bundles.LineBundle.IsAmple.projectivePresentation {L : Line.Bundles.LineBundle X}
    (hL : L.IsAmple) (f : X ⟶ S) [IsProper f] [IsAffine S] :
    Projective.ProjectivePresentations.ProjectivePresentation (Over.mk f) :=
  (hL.exists_projectivePresentation f).some

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
