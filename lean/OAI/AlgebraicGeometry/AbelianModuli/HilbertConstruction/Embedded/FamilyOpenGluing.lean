import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyMatching
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyCoverEquality

/-! # Family Open Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded

noncomputable section

/-! Matching embedded flat families on an arbitrary small open base cover glue uniquely. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {P T : Over S} {C : Scheme.OpenCover.{u} T.left}
variable (D : FamilyMatching.EmbeddedFamilyMatchingData P T C)

/-- Glue a matching family by gluing its locally directed affine refinement. -/
def FamilyMatching.EmbeddedFamilyMatchingData.glue : Closed.Families.FlatClosedFamily (FamilyFunctor.embeddedFamilyAmbient P T) := D.refinement.glue

theorem FamilyMatching.EmbeddedFamilyMatchingData.glue_refinement_pullback (k : (Directed.OpenRefinement.directedOpenRefinement C).I₀) :
    (FamilyFunctor.embeddedFlatFamilyFunctor P).map (FamilyOpenCover.overOpenCoverMap T (Directed.OpenRefinement.directedOpenRefinement C) k).op D.glue =
      (FamilyFunctor.embeddedFlatFamilyFunctor P).map (FamilyMatching.directedRefinementOverMap T C k).op (D.family k.1) :=
  D.refinement.glue_pullback k

/-- A family matching the affine refinement matches the original cover. -/
theorem FamilyMatching.EmbeddedFamilyMatchingData.restrict_of_refinement (F : Closed.Families.FlatClosedFamily (FamilyFunctor.embeddedFamilyAmbient P T))
    (hF : ∀ k : (Directed.OpenRefinement.directedOpenRefinement C).I₀,
      (FamilyFunctor.embeddedFlatFamilyFunctor P).map (FamilyOpenCover.overOpenCoverMap T (Directed.OpenRefinement.directedOpenRefinement C) k).op F =
        (FamilyFunctor.embeddedFlatFamilyFunctor P).map (FamilyMatching.directedRefinementOverMap T C k).op (D.family k.1))
    (i : C.I₀) :
    (FamilyFunctor.embeddedFlatFamilyFunctor P).map (FamilyOpenCover.overOpenCoverMap T C i).op F = D.family i := by
  let V (v : (C.X i).affineOpens) : Over S :=
    FamilyOpenCover.overOpenCoverObject T (Directed.OpenRefinement.directedOpenRefinement C) ⟨i, v⟩
  let f (v : (C.X i).affineOpens) : V v ⟶ FamilyOpenCover.overOpenCoverObject T C i :=
    FamilyMatching.directedRefinementOverMap T C ⟨i, v⟩
  have (v : (C.X i).affineOpens) : IsOpenImmersion (f v).left :=
    inferInstanceAs (IsOpenImmersion v.1.ι)
  have hc : ∀ x : (FamilyOpenCover.overOpenCoverObject T C i).left, ∃ v y, (f v).left y = x := by
    intro x
    obtain ⟨v, y, hy⟩ := (C.X i).directedAffineCover.exists_eq x
    exact ⟨v, y, hy⟩
  apply FamilyCoverEquality.embeddedFlatFamily_eq_of_covering_maps V f hc
    ((FamilyFunctor.embeddedFlatFamilyFunctor P).map (FamilyOpenCover.overOpenCoverMap T C i).op F) (D.family i)
  intro v
  have he : F.ideal.comap
      (FamilyFunctor.embeddedFamilyAmbientMap P (FamilyOpenCover.overOpenCoverMap T (Directed.OpenRefinement.directedOpenRefinement C) ⟨i, v⟩)) =
      (D.family i).ideal.comap (FamilyFunctor.embeddedFamilyAmbientMap P (f v)) :=
    congrArg Closed.Families.FlatClosedFamily.ideal (hF ⟨i, v⟩)
  apply Closed.Families.FlatClosedFamily.ext
  change (F.ideal.comap (FamilyFunctor.embeddedFamilyAmbientMap P (FamilyOpenCover.overOpenCoverMap T C i))).comap
    (FamilyFunctor.embeddedFamilyAmbientMap P (f v)) = (D.family i).ideal.comap (FamilyFunctor.embeddedFamilyAmbientMap P (f v))
  rw [← Scheme.IdealSheafData.comap_comp, ← PullbackIdentity.embeddedFamilyAmbientMap_comp]
  have hf : f v ≫ FamilyOpenCover.overOpenCoverMap T C i =
      FamilyOpenCover.overOpenCoverMap T (Directed.OpenRefinement.directedOpenRefinement C) ⟨i, v⟩ := FamilyMatching.directedRefinementOverMap_base T C ⟨i, v⟩
  exact (congrArg (fun a => F.ideal.comap (FamilyFunctor.embeddedFamilyAmbientMap P a)) hf).trans he

/-- The global family's restrictions recover every member of the original open cover. -/
theorem FamilyMatching.EmbeddedFamilyMatchingData.glue_pullback (i : C.I₀) :
    (FamilyFunctor.embeddedFlatFamilyFunctor P).map (FamilyOpenCover.overOpenCoverMap T C i).op D.glue = D.family i :=
  D.restrict_of_refinement D.glue D.glue_refinement_pullback i

/-- An arbitrary matching family on a small open cover glues to a unique embedded flat family. -/
theorem FamilyMatching.EmbeddedFamilyMatchingData.existsUnique_glue : ∃! F : Closed.Families.FlatClosedFamily (FamilyFunctor.embeddedFamilyAmbient P T),
    ∀ i, (FamilyFunctor.embeddedFlatFamilyFunctor P).map (FamilyOpenCover.overOpenCoverMap T C i).op F = D.family i := by
  refine ⟨D.glue, D.glue_pullback, ?_⟩
  intro F hF
  exact FamilyOpenCover.embeddedFlatFamily_eq_of_open_cover C F D.glue
    (fun i => (hF i).trans (D.glue_pullback i).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded
