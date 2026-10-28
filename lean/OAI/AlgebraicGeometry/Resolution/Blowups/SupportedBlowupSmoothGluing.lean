import OAI.AlgebraicGeometry.Resolution.Blowups.SupportedCenterBlowup

/-! # Supported Blowup Smooth Gluing -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.SupportedBlowupSmoothGluing.Construction

noncomputable section

/-! Smoothness gluing for a supported blowup step: the local blowup
and the unchanged complement form an actual open cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem opensRange_of_open_pullback
    {X' X Y' Y : Scheme.{u}} (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (j : Y' ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (hpb : IsPullback i f' f j) :
    i.opensRange = f ⁻¹ᵁ j.opensRange := by
  have he : (hpb.isoPullback.hom ≫ pullback.fst f j).opensRange = i.opensRange := by
    congr 1
    exact hpb.isoPullback_hom_fst
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_pullbackFst] at he
  exact he.symm

theorem smooth_on_opensRange_of_open_immersion
    {X U Z : Scheme.{u}} (f : X ⟶ Z) (j : U ⟶ X) [IsOpenImmersion j]
    [Smooth (j ≫ f)] : Smooth (j.opensRange.ι ≫ f) := by
  have he : Set.range j = Set.range j.opensRange.ι := by
    rw [Scheme.Opens.range_ι]
    rfl
  let e := IsOpenImmersion.isoOfRangeEq j j.opensRange.ι he
  have heq : e.inv ≫ j = j.opensRange.ι := IsOpenImmersion.isoOfRangeEq_inv_fac j _ he
  let : Smooth (e.inv ≫ (j ≫ f)) := inferInstance
  have h : Smooth ((e.inv ≫ j) ≫ f) := by simpa only [Category.assoc] using
    (inferInstance : Smooth (e.inv ≫ (j ≫ f)))
  rw [heq] at h
  exact h

theorem smooth_of_two_source_opens
    {X Z : Scheme.{u}} (f : X ⟶ Z) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [Smooth (U.ι ≫ f)] [Smooth (V.ι ≫ f)] : Smooth f := by
  let : IsZariskiLocalAtSource @AlgebraicGeometry.Smooth.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Smooth)
  let W : Bool → X.Opens := fun b => if b then U else V
  have hW : iSup W = ⊤ := by
    simpa only [W, iSup_bool_eq, Bool.false_eq_true, ite_false, ite_true, sup_comm V U] using hcover
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth) W hW
  intro b
  cases b
  · exact (inferInstance : Smooth (V.ι ≫ f))
  · exact (inferInstance : Smooth (U.ι ≫ f))

/-- A modification is smooth over the original base if its local
description is smooth and the complementary region is unchanged.
The two regions cover the whole source by the actual pullback square. -/
theorem smooth_of_local_pullback_and_iso_complement
    {X' X Y' Y Z : Scheme.{u}} (i : X' ⟶ X) (f' : X' ⟶ Y') (π : X ⟶ Y)
    (j : Y' ⟶ Y) (f : Y ⟶ Z) [IsOpenImmersion j] (hpb : IsPullback i f' π j)
    (V : Y.Opens) (hcover : j.opensRange ⊔ V = ⊤)
    [Smooth f] [Smooth (f' ≫ j ≫ f)] [IsIso (π ∣_ V)] : Smooth (π ≫ f) := by
  let : IsOpenImmersion i :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb.flip inferInstance
  have hirange := opensRange_of_open_pullback i f' π j hpb
  have hsourcecover : i.opensRange ⊔ π ⁻¹ᵁ V = ⊤ := by
    rw [hirange, ← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]
  let : Smooth (i ≫ (π ≫ f)) := by
    rw [← Category.assoc, hpb.w, Category.assoc]
    infer_instance
  let : Smooth (i.opensRange.ι ≫ (π ≫ f)) :=
    smooth_on_opensRange_of_open_immersion (π ≫ f) i
  let : Smooth ((π ⁻¹ᵁ V).ι ≫ (π ≫ f)) := by
    rw [← Category.assoc, ← morphismRestrict_ι π V, Category.assoc]
    infer_instance
  exact smooth_of_two_source_opens (π ≫ f) i.opensRange (π ⁻¹ᵁ V) hsourcecover

end

end OAI.AlgebraicGeometry.Resolution.Blowups.SupportedBlowupSmoothGluing.Construction
