import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.AmplePullbackFinite
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FiniteSectionAmpleness
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FiniteLocus
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.HyperplanePowers

/-! # Generated Fiber Ample Neighborhood -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeneratedFiberAmpleNeighborhood

noncomputable section

/-! Given generating sections on the family, ampleness on any geometric
coefficient fiber implies ampleness on an affine neighborhood of its base
point. The proof uses the actual hyperplane pullback and finite-family locus. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace PolarizationEmbedding
variable {X S : Scheme.{0}} (f : X ⟶ S) [IsProper f] [IsAffine S]
variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) {n : ℕ}
variable (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf))
variable (hs : ∀ x : X, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))

theorem section_baseChange_finite_of_ample_fiber {T : Scheme.{0}}
    (g : T ⟶ Spec (.of Γ(S, ⊤)))
    (hL : (L.pullback (pullback.fst
      (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs ≫ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom) g)).IsAmple) :
    IsFinite (HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)
      (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom g) := by
  have : IsProper (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) := AbelianModuli.HilbertConstruction.Affine.SectionMorphism.sectionAbsoluteMorphism_proper f s hs
  obtain ⟨e⟩ := Section.HyperplanePullback.PolarizationEmbedding.exists_sectionHyperplane_pullback_iso f s hs (0 : Fin (n + 1))
  exact Relative.AmplePullbackFinite.relativeMorphismBaseChange_isFinite_of_ample_pullback _ _
    (Projective.HyperplanePowers.PolarizationEmbedding.projectiveHyperplaneLine Γ(S, ⊤) n 0) L e g hL

theorem exists_affine_ample_neighborhood_of_generated_ample_fiber
    {K : Type} [Field K] (g : Spec (.of K) ⟶ Spec (.of Γ(S, ⊤)))
    (hL : (L.pullback (pullback.fst
      (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs ≫ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom) g)).IsAmple) :
    ∃ U : (Spec (.of Γ(S, ⊤))).Opens,
      g (IsLocalRing.closedPoint K) ∈ U ∧ IsAffineOpen U ∧
        (L.pullback (pullback.fst
          (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs ≫ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom) U.ι)).IsAmple := by
  let a := AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs
  let q := (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom
  have : IsProper a := AbelianModuli.HilbertConstruction.Affine.SectionMorphism.sectionAbsoluteMorphism_proper f s hs
  have hfin : IsFinite (HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange a q g) :=
    section_baseChange_finite_of_ample_fiber f L s hs g hL
  have hb : g (IsLocalRing.closedPoint K) ∈ Proper.RelativeFiniteNeighborhood.properRelativeFiniteOpen a q :=
    (Relative.FiniteLocus.relativeMorphismBaseChange_isFinite_iff_range a q g).mp hfin ⟨_, rfl⟩
  obtain ⟨U, hU, hbU, hsub⟩ := exists_isAffineOpen_mem_and_subset hb
  refine ⟨U, hbU, hU, ?_⟩
  have : IsAffine U.toScheme := hU
  apply Relative.FiniteSectionAmpleness.PolarizationEmbedding.isAmple_after_finite_section_baseChange f L s hs U.ι
  apply Proper.RelativeFiniteNeighborhood.relativeMorphismBaseChange_isFinite_of_range_subset a q
  rw [Scheme.Opens.range_ι]
  exact hsub

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeneratedFiberAmpleNeighborhood
