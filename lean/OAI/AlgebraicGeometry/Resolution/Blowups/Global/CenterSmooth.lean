import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.ComparisonGluing
import OAI.AlgebraicGeometry.Resolution.Blowups.SupportedBlowupSmoothGluing

/-! # Center Smooth -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.CenterSmooth.Construction

noncomputable section

/-! Smoothness of an actual globally glued center from its local restrictions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

/-- Smoothness of the closed center glues through its actual pullback
subschemes on an open cover of the ambient scheme. -/
theorem idealSheaf_subscheme_smooth_of_open_restrictions
    {X Z : Scheme.{u}} {ι : Type v} (I : X.IdealSheafData) (f : X ⟶ Z)
    (U : ι → X.Opens) (hcover : ⨆ i, U i = ⊤)
    (hlocal : ∀ i, Smooth ((I.comap (U i).ι).subschemeι ≫ (U i).ι ≫ f)) :
    Smooth (I.subschemeι ≫ f) := by
  let k : ∀ i, (I.comap (U i).ι).subscheme ⟶ I.subscheme := fun i =>
    (I.comapIso (U i).ι).hom ≫ pullback.snd (U i).ι I.subschemeι
  have hcomp (i : ι) : k i ≫ I.subschemeι = (I.comap (U i).ι).subschemeι ≫ (U i).ι := by
    dsimp only [k]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      Scheme.IdealSheafData.comapIso_hom_fst]
  have hrange (i : ι) : (k i).opensRange = I.subschemeι ⁻¹ᵁ U i := by
    dsimp only [k]
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_pullbackSnd,
      Scheme.Opens.opensRange_ι]
  have hsource : ⨆ i, (k i).opensRange = ⊤ := by
    simp_rw [hrange]
    rw [← Scheme.Hom.preimage_iSup, hcover, Scheme.Hom.preimage_top]
  let : IsZariskiLocalAtSource @AlgebraicGeometry.Smooth.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Smooth)
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth)
    (fun i => (k i).opensRange) hsource
  intro i
  let : Smooth (k i ≫ (I.subschemeι ≫ f)) := by
    rw [← Category.assoc, hcomp, Category.assoc]
    exact hlocal i
  exact SupportedBlowupSmoothGluing.Construction.smooth_on_opensRange_of_open_immersion (I.subschemeι ≫ f) (k i)

/-- It suffices to check the actual affine Rees blowups on a chosen affine
open cover; their smoothness glues to the already constructed global blowup. -/
theorem globalBlowup_smooth_of_affine_cover
    {X Z : Scheme.{u}} {ι : Type v} [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (f : X ⟶ Z)
    (U : ι → X.affineOpens) (hcover : ⨆ i, (U i).1 = ⊤)
    (hlocal : ∀ i, Smooth (ReesGrading.Construction.affineBlowupToSpec (I.ideal (U i)) ≫ (U i).2.fromSpec ≫ f)) :
    Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := by
  have hrange (i : ι) : (GlobalBlowup.Data.Construction.globalBlowupChart I hI (U i)).opensRange =
      GlobalBlowup.Data.Construction.globalBlowupToBase I hI ⁻¹ᵁ (U i).1 := by
    have h := SupportedBlowupSmoothGluing.Construction.opensRange_of_open_pullback (GlobalBlowup.Data.Construction.globalBlowupChart I hI (U i))
      (ReesGrading.Construction.affineBlowupToSpec (I.ideal (U i)) ≫ (U i).2.isoSpec.inv)
      (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) (U i).1.ι (GlobalBlowup.Data.Construction.globalBlowup_affineOpen_isPullback I hI (U i))
    rwa [Scheme.Opens.opensRange_ι] at h
  have hsource : ⨆ i, (GlobalBlowup.Data.Construction.globalBlowupChart I hI (U i)).opensRange = ⊤ := by
    simp_rw [hrange]
    rw [← Scheme.Hom.preimage_iSup, hcover, Scheme.Hom.preimage_top]
  let : IsZariskiLocalAtSource @AlgebraicGeometry.Smooth.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Smooth)
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth)
    (fun i => (GlobalBlowup.Data.Construction.globalBlowupChart I hI (U i)).opensRange) hsource
  intro i
  let : Smooth (GlobalBlowup.Data.Construction.globalBlowupChart I hI (U i) ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)) := by
    rw [← Category.assoc, GlobalBlowup.Data.Construction.globalBlowupChart_over, Category.assoc]
    exact hlocal i
  exact SupportedBlowupSmoothGluing.Construction.smooth_on_opensRange_of_open_immersion (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
    (GlobalBlowup.Data.Construction.globalBlowupChart I hI (U i))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.CenterSmooth.Construction
