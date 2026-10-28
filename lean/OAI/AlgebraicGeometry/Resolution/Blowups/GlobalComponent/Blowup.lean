import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.Center
import OAI.AlgebraicGeometry.Resolution.Blowups.IsomorphicBlowupEquiv

/-! # Blowup -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent

noncomputable section

/-! The actual canonical global component blowup and its proved geometry. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem Blowup.Construction.globalBlowup_isIso_of_chosen_affine_cover
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) {ι : Type}
    (U : ι → X.affineOpens) (hcover : ⨆ i, (U i).val = ⊤)
    (h : ∀ i, IsIso (ReesGrading.Construction.affineBlowupToSpec (I.ideal (U i)))) :
    IsIso (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms Scheme)
    (Global.MonomialBoundaryAtlas.Construction.chosenAffineSpecCover U hcover).openCover
  intro i
  change IsIso (pullback.snd (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) (U i).2.fromSpec)
  let : IsIso (ReesGrading.Construction.affineBlowupToSpec (I.ideal (U i))) := h i
  rw [← (GlobalBlowup.MapGluing.Construction.globalBlowup_affineSpec_isPullback I hI (U i)).isoPullback_inv_snd]
  infer_instance

theorem ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.center_blowup_isIso
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {n : ℕ} (A : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) :
    IsIso (GlobalBlowup.Data.Construction.globalBlowupToBase A.center A.center_ne_bot) := by
  apply Blowup.Construction.globalBlowup_isIso_of_chosen_affine_cover A.center A.center_ne_bot A.nativeOpens A.nativeOpens_cover
  intro i
  rw [A.center_ideal i]
  let : IsIso (ReesGrading.Construction.affineBlowupToSpec (A.choice i).center) := (A.choice i).blowup_isIso
  exact IsomorphicBlowupEquiv.Construction.affineBlowup_isIso_of_comap_equiv (Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv (A.rings i) (A.map i)) _

theorem Blowup.Construction.exists_global_coefficient_component_step
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (n : ℕ)
    (hbound : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (n + 1) = ⊤) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∃ (I : X.IdealSheafData) (hI : I ≠ ⊥),
      J ≤ I ^ (n + 1) ∧ Smooth (I.subschemeι ≫ f) ∧
      IsIso (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) ∧ Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨A⟩ := ChoiceAtlas.Construction.exists_global_component_choice_atlas f J n hbound
  let : IsIso (GlobalBlowup.Data.Construction.globalBlowupToBase A.center A.center_ne_bot) := A.center_blowup_isIso
  exact ⟨A.center, A.center_ne_bot, A.center_permissible, A.center_smooth, inferInstance, inferInstance⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent
