import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.SectionAmpleness
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.RelativeFiniteNeighborhood

/-! # Finite Section Ampleness -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FiniteSectionAmpleness

noncomputable section

/-! A finite coefficient fiber of an actual section morphism gives
ampleness over an affine base neighborhood. The sections are retained,
and no relative-ampleness assumption is made in this step. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace PolarizationEmbedding
universe u
variable {X S T : Scheme.{u}} (f : X ⟶ S) [IsProper f] [IsAffine S]
variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) {n : ℕ}
variable (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf))
variable (hs : ∀ x : X, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))

theorem isAmple_after_finite_section_baseChange [IsAffine T]
    (g : T ⟶ Spec (.of Γ(S, ⊤)))
    (h : IsFinite (HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)
      (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom g)) :
    (L.pullback (pullback.fst
      (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs ≫ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom) g)).IsAmple := by
  let a := AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs
  let q := (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom
  let e := HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange a q g
  have : IsProper a := AbelianModuli.HilbertConstruction.Affine.SectionMorphism.sectionAbsoluteMorphism_proper f s hs
  have : IsFinite e := h
  have : IsAffineHom g := inferInstance
  have : IsAffineHom (pullback.fst q g) := MorphismProperty.pullback_fst _ _ inferInstance
  have : CompactSpace (pullback (a ≫ q) g : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd (a ≫ q) g)
  have he : e ≫ pullback.fst q g = pullback.fst (a ≫ q) g ≫ a := by
    simp only [e, HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange, pullback.map, pullback.lift_fst]
  have : IsAffineHom (pullback.fst (a ≫ q) g ≫ a) := by
    rw [← he]
    infer_instance
  exact Affine.SectionAmpleness.PolarizationEmbedding.isAmple_pullback_of_affine_section_composite f L s hs (pullback.fst (a ≫ q) g)

theorem exists_affine_ample_neighborhood_of_finite_section_fiber
    (b : Spec (.of Γ(S, ⊤)))
    (h : IsFinite (HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)
      (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom ((Spec (.of Γ(S, ⊤))).fromSpecResidueField b))) :
    ∃ U : (Spec (.of Γ(S, ⊤))).Opens, b ∈ U ∧ IsAffineOpen U ∧
      (L.pullback (pullback.fst
        (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs ≫ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom) U.ι)).IsAmple := by
  let a := AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs
  let q := (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom
  have : IsProper a := AbelianModuli.HilbertConstruction.Affine.SectionMorphism.sectionAbsoluteMorphism_proper f s hs
  have hb : b ∈ Proper.RelativeFiniteNeighborhood.properRelativeFiniteOpen a q :=
    Proper.RelativeFiniteNeighborhood.mem_properRelativeFiniteOpen_of_finite_fiber a q b h
  obtain ⟨U, hU, hbU, hsub⟩ := exists_isAffineOpen_mem_and_subset hb
  refine ⟨U, hbU, hU, ?_⟩
  have : IsAffine U.toScheme := hU
  apply isAmple_after_finite_section_baseChange f L s hs U.ι
  apply Proper.RelativeFiniteNeighborhood.relativeMorphismBaseChange_isFinite_of_range_subset a q
  rw [Scheme.Opens.range_ι]
  exact hsub

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FiniteSectionAmpleness
