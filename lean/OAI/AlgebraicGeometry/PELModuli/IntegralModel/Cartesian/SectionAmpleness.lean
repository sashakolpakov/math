import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeneratedFiberAmpleNeighborhood

/-! # Section Ampleness -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.SectionAmpleness

noncomputable section

/-! Section-morphism finiteness and ampleness retain an arbitrary actual
cartesian square over the original affine base. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace PolarizationEmbedding
universe u

theorem isAmple_pullback_iff_of_cartesian
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (a : Y ⟶ X) (ρ : Y ⟶ T) (g : T ⟶ S) (hp : IsPullback a ρ f g) :
    (L.pullback a).IsAmple ↔ (L.pullback (pullback.fst f g)).IsAmple := by
  constructor
  · intro hL
    let e : ((L.pullback a).pullback hp.isoPullback.inv).sheaf ≅
        (L.pullback (pullback.fst f g)).sheaf :=
      (Scheme.Modules.pullbackComp hp.isoPullback.inv a).app L.sheaf ≪≫
        (Scheme.Modules.pullbackCongr hp.isoPullback_inv_fst).app L.sheaf
    exact (hL.pullback_of_isIso hp.isoPullback.inv).of_iso e
  · intro hL
    let e : ((L.pullback (pullback.fst f g)).pullback hp.isoPullback.hom).sheaf ≅
        (L.pullback a).sheaf :=
      (Scheme.Modules.pullbackComp hp.isoPullback.hom (pullback.fst f g)).app L.sheaf ≪≫
        (Scheme.Modules.pullbackCongr hp.isoPullback_hom_fst).app L.sheaf
    exact (hL.pullback_of_isIso hp.isoPullback.hom).of_iso e

variable {X Y S T : Scheme.{0}} (f : X ⟶ S) [IsAffine S]
variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) {n : ℕ}
variable (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf))
variable (hs : ∀ x : X, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
variable (a : Y ⟶ X) (ρ : Y ⟶ T) (g : T ⟶ S) (hp : IsPullback a ρ f g)
include hp hs

theorem sectionCoefficient_isPullback : IsPullback a ρ
    (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs ≫ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom)
    (g ≫ S.toSpecΓ) := by
  rw [AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism_over]
  have h : IsPullback g (𝟙 T) S.toSpecΓ (g ≫ S.toSpecΓ) :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  simpa only [Category.comp_id] using hp.paste_vert h

theorem section_finite_of_cartesian_ample [IsProper f]
    (hL : (L.pullback a).IsAmple) :
    IsFinite (HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)
      (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom (g ≫ S.toSpecΓ)) := by
  have H : IsPullback a ρ
      (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs ≫ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom)
      (g ≫ S.toSpecΓ) := sectionCoefficient_isPullback f L s hs a ρ g hp
  have hcan : (L.pullback (pullback.fst
      (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs ≫ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom)
      (g ≫ S.toSpecΓ))).IsAmple :=
    (isAmple_pullback_iff_of_cartesian
      (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs ≫ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom)
      L a ρ (g ≫ S.toSpecΓ) H).mp hL
  exact GeneratedFiberAmpleNeighborhood.PolarizationEmbedding.section_baseChange_finite_of_ample_fiber (X := X) (S := S) (T := T)
    f L s hs (g ≫ S.toSpecΓ) hcan

theorem cartesian_isAmple_of_section_finite [IsProper f] [IsAffine T]
    (h : IsFinite (HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)
      (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom (g ≫ S.toSpecΓ))) :
    (L.pullback a).IsAmple := by
  let H := sectionCoefficient_isPullback f L s hs a ρ g hp
  exact (isAmple_pullback_iff_of_cartesian _ L a ρ _ H).mpr
    (Relative.FiniteSectionAmpleness.PolarizationEmbedding.isAmple_after_finite_section_baseChange f L s hs (g ≫ S.toSpecΓ) h)

theorem exists_affine_ample_neighborhood_of_cartesian_generated_ample
    [IsProper f] (t : T) (hL : (L.pullback a).IsAmple) :
    ∃ U : S.Opens, g t ∈ U ∧ IsAffineOpen U ∧
      (L.pullback (f ⁻¹ᵁ U).ι).IsAmple := by
  let A := AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs
  let q := (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom
  have : IsProper A := AbelianModuli.HilbertConstruction.Affine.SectionMorphism.sectionAbsoluteMorphism_proper f s hs
  have hfin := section_finite_of_cartesian_ample f L s hs a ρ g hp hL
  have hb : S.toSpecΓ (g t) ∈ Proper.RelativeFiniteNeighborhood.properRelativeFiniteOpen A q :=
    (Relative.FiniteLocus.relativeMorphismBaseChange_isFinite_iff_range A q (g ≫ S.toSpecΓ)).mp hfin ⟨t, rfl⟩
  obtain ⟨U, hU, htU, hsub⟩ := exists_isAffineOpen_mem_and_subset
    (show g t ∈ S.toSpecΓ ⁻¹ᵁ Proper.RelativeFiniteNeighborhood.properRelativeFiniteOpen A q from hb)
  refine ⟨U, htU, hU, ?_⟩
  have : IsAffine U.toScheme := hU
  apply cartesian_isAmple_of_section_finite f L s hs (f ⁻¹ᵁ U).ι
    (f ∣_ U) U.ι (isPullback_morphismRestrict f U).flip
  apply Proper.RelativeFiniteNeighborhood.relativeMorphismBaseChange_isFinite_of_range_subset A q
  rintro _ ⟨y, rfl⟩
  exact hsub y.property

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.SectionAmpleness
