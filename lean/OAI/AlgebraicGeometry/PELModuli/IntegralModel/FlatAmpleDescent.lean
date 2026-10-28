import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatSectionGenerationDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.SectionAmpleness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.FiniteMorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange

/-! # Flat Ample Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatAmpleDescent

noncomputable section

/-! Ampleness descends through a surjective flat affine coefficient
change for a proper flat family over a noetherian affine base. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.SectionAmpleness.PolarizationEmbedding

theorem properFlat_isAmple_of_flat_surjective_baseChange
    {X Y S T : Scheme.{0}} [IsAffine S] [IsAffine T] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (a : Y ⟶ X) (ρ : Y ⟶ T) (g : T ⟶ S) (hp : IsPullback a ρ f g)
    (hg : g.appTop.hom.Flat) [Surjective g]
    (hL : (L.pullback a).IsAmple) : L.IsAmple := by
  have : Surjective a := MorphismProperty.of_isPullback (P := @Surjective) hp.flip inferInstance
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨d, hd, k, t, ht, _⟩ := hL.projective_section_family
  let e := L.powerBaseChangeIso a d
  have hgeneration : ∀ y : Y, ∃ s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶
      ((L.tensorPower d).pullback a).sheaf, y ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s := by
    intro y
    obtain ⟨i, hi⟩ := ht y
    exact ⟨t i ≫ e.inv, (AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso (t i) e.symm).symm ▸ hi⟩
  obtain ⟨n, s, hs⟩ := FlatSectionGenerationDescent.properFlat_exists_generating_sections_of_flat_baseChange
    f (L.tensorPower d) a ρ g hp hg a.surjective hgeneration
  let A := AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs
  let q := (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom
  have : IsProper A := AbelianModuli.HilbertConstruction.Affine.SectionMorphism.sectionAbsoluteMorphism_proper f s hs
  have hfin := Cartesian.SectionAmpleness.PolarizationEmbedding.section_finite_of_cartesian_ample f (L.tensorPower d) s hs a ρ g hp
    ((hL.tensorPower d hd).of_iso e.symm)
  have hb := (Relative.FiniteLocus.relativeMorphismBaseChange_isFinite_iff_range A q (g ≫ S.toSpecΓ)).mp hfin
  have hsurj : Function.Surjective (g ≫ S.toSpecΓ) :=
    S.toSpecΓ.surjective.comp g.surjective
  have : IsFinite A := by
    apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @IsFinite)
    intro y
    apply (MaximalFiniteOpen.mem_maximalFiniteOpen A y).mp
    exact (Proper.RelativeFiniteNeighborhood.mem_properRelativeFiniteOpen A q (q y)).mp
      (hb (Set.range_eq_univ.mpr hsurj ▸ Set.mem_univ (q y))) y rfl
  exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsAmple.of_tensorPower d hd
    (Affine.SectionAmpleness.PolarizationEmbedding.isAmple_of_affine_section_morphism f (L.tensorPower d) s hs)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatAmpleDescent
