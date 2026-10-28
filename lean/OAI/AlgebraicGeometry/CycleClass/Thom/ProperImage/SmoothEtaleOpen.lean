import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.GenericEtale
import OAI.AlgebraicGeometry.CycleClass.Geometric.SmoothStratum

/-! # Smooth Etale Open -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.SmoothEtaleOpen.Constructions.Construction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

/-- The finite etale generic open can be chosen inside the target smooth
locus. Its entire inverse image is then smooth as well. -/
theorem exists_generic_smooth_finiteEtale_open
    {S T : Scheme} [IsIntegral S] [IsIntegral T]
    (i : S ⟶ T) (g : T ⟶ Spec (.of ℂ))
    [IsProper i] [LocallyOfFinitePresentation i] [LocallyOfFinitePresentation g]
    (hη : i (genericPoint S) = genericPoint T)
    (hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ g)) :
    ∃ W : T.Opens, genericPoint T ∈ W ∧
      IsFinite (i ∣_ W) ∧ Etale (i ∣_ W) ∧
      Smooth (W.ι ≫ g) ∧ Smooth ((i ⁻¹ᵁ W).ι ≫ (i ≫ g)) := by
  obtain ⟨U, hU, hfin, het⟩ := GenericEtale.Constructions.Construction.exists_generic_finiteEtale_open i g hη hdim
  let : IsFinite (i ∣_ U) := hfin
  let : Etale (i ∣_ U) := het
  let W := U ⊓ g.smoothLocus
  have hW : U.ι ''ᵁ (U.ι ⁻¹ᵁ g.smoothLocus) = W := by
    simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, W]
  let e := morphismRestrictRestrict i U (U.ι ⁻¹ᵁ g.smoothLocus) ≪≫ morphismRestrictEq i hW
  let : MorphismProperty.RespectsIso (@IsFinite.{0} : MorphismProperty Scheme.{0}) := by
    apply MorphismProperty.RespectsIso.mk
    · intro A B C e f hf
      let : IsFinite f := hf
      infer_instance
    · intro A B C e f hf
      let : IsFinite f := hf
      infer_instance
  let : MorphismProperty.RespectsIso (@Etale.{0} : MorphismProperty Scheme.{0}) := by
    apply MorphismProperty.RespectsIso.mk
    · intro A B C e f hf
      let : Etale f := hf
      infer_instance
    · intro A B C e f hf
      let : Etale f := hf
      infer_instance
  let : IsFinite (i ∣_ W) := (MorphismProperty.arrow_mk_iso_iff
    (@IsFinite.{0} : MorphismProperty Scheme.{0}) e).mp inferInstance
  let : Etale (i ∣_ W) := (MorphismProperty.arrow_mk_iso_iff
    (@Etale.{0} : MorphismProperty Scheme.{0}) e).mp inferInstance
  let : Smooth (g.smoothLocus.ι ≫ g) := Geometric.SmoothStratum.smoothStratumToBase_isSmooth g
  have hle : W ≤ g.smoothLocus := inf_le_right
  let : Smooth (W.ι ≫ g) := by
    rw [← T.homOfLE_ι hle, Category.assoc]
    infer_instance
  refine ⟨W, ⟨hU, g.genericPoint_mem_smoothLocus_of_perfectField⟩,
    inferInstance, inferInstance, inferInstance, ?_⟩
  rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  infer_instance

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.SmoothEtaleOpen.Constructions.Construction
