import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SelectedSectionImmersion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.ProjectivePresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveImmersions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceOverComposition
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Quasi Projective Presentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A separated finite-type scheme with an ample line bundle over an affine base has a constructed immersion in projective space. Over a Noetherian base its actual image closure provides a quasi-projective presentation. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem Line.Bundles.LineBundle.IsAmple.exists_projectiveImmersion
    {X S : Scheme.{u}} [X.IsSeparated] [IsAffine S] {L : Line.Bundles.LineBundle X}
    (hL : L.IsAmple) (f : X ⟶ S) [LocallyOfFiniteType f] :
    ∃ (n : ℕ) (a : Over.mk f ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n), IsImmersion a.left := by
  have : CompactSpace X := ⟨hL.1⟩
  obtain ⟨d, _, k, s, hs, ha⟩ := hL.projective_section_family
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
  have habs : IsImmersion (SectionsProjectiveMorphism.sectionAbsoluteMorphism f q hqcover) :=
    SelectedSectionImmersion.sectionAbsoluteMorphism_immersion_of_selected f q hqcover j hcover haq hgen
  let a := SectionsProjectiveMorphism.sectionProjectiveMorphism f q hqcover
  let p : (Projective.ProjectivePresentations.projectiveSpaceOver S n).left ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).left :=
    pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ
  have hp : a.left ≫ p = SectionsProjectiveMorphism.sectionAbsoluteMorphism f q hqcover := pullback.lift_fst _ _ _
  have : IsImmersion (a.left ≫ p) := hp.symm ▸ habs
  exact ⟨n, a, IsImmersion.of_comp a.left p⟩

theorem Line.Bundles.LineBundle.IsAmple.exists_quasiProjectivePresentation
    {X S : Scheme.{u}} [X.IsSeparated] [IsAffine S] [IsNoetherian S] {L : Line.Bundles.LineBundle X}
    (hL : L.IsAmple) (f : X ⟶ S) [LocallyOfFiniteType f] :
    Nonempty (Projective.ProjectivePresentations.QuasiProjectivePresentation (Over.mk f)) := by
  have : CompactSpace X := ⟨hL.1⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := ⟨⟩
  have hX : TopologicalSpace.NoetherianSpace X := IsNoetherian.noetherianSpace
  obtain ⟨n, a, ha⟩ := hL.exists_projectiveImmersion f
  have : IsImmersion a.left := ha
  have : QuasiCompact a.left := by
    constructor
    intro U _ _
    exact @TopologicalSpace.NoetherianSpace.isCompact X _ hX (a.left ⁻¹' U)
  exact ⟨(Projective.SpaceOverComposition.projectiveSpaceIdentityPresentation S n).quasiProjectiveImmersion a⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
