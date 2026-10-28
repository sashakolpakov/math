import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalSurface.ReferenceTransformBound
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.BoundTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.Clearance

/-! # Refined Surface Coefficient Bound -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Actual refinements isomorphic to the canonical blowup retain its strict coefficient-bound decrease. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.refined_surfaceCenter_bound
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData} {n : ℕ}
    (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (ℓ : ℕ)
    (hb : ∀ i, (A.choice i).HasBound (ℓ + 1)) (hd : ∀ i, ringKrullDim (A.rings i) ≤ 2)
    (hlevel : (n + 1).factorial ≤ ℓ + 1) (hbound : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (n + 1) = ⊤)
    {Y : Scheme} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData}
    (e : Y ≅ GlobalBlowup.Data.Construction.globalBlowup (A.surfaceCenter ℓ hb hd hlevel) (A.surfaceCenter_nonzero ℓ hb hd hlevel))
    (hg : e.hom ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase (A.surfaceCenter ℓ hb hd hlevel)
      (A.surfaceCenter_nonzero ℓ hb hd hlevel) ≫ f) = g)
    (hK : (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal (A.surfaceCenter ℓ hb hd hlevel) J
      (A.surfaceCenter_nonzero ℓ hb hd hlevel) (n + 1)).comap e.hom = K)
    (B : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas g K n) : ∀ i, (B.choice i).HasBound ℓ := by
  let I := A.surfaceCenter ℓ hb hd hlevel
  let hI : I ≠ ⊥ := A.surfaceCenter_nonzero ℓ hb hd hlevel
  let π := GlobalBlowup.Data.Construction.globalBlowupToBase I hI
  let : Smooth (π ≫ f) := A.surfaceCenter_isBlowupSmooth ℓ hb hd hlevel
  let : CompactSpace (GlobalBlowup.Data.Construction.globalBlowup I hI) := QuasiCompact.compactSpace_of_compactSpace π
  have hB : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (π ≫ f) (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + 1)) (n + 1) = ⊤ :=
    Global.OrderBoundPreservation.Construction.globalBlowup_preserves_differential_order_bound f I J hI (n + 1)
      (A.surfaceCenter_isPermissible ℓ hb hd hlevel) hbound
  obtain ⟨C⟩ := GlobalComponent.ChoiceAtlas.Construction.exists_global_component_choice_atlas (π ≫ f) (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + 1)) n hB
  exact C.hasBound_transport_etale B e.hom hg hK ℓ (A.surfaceCenter_original_transform_bound ℓ hb hd hlevel hbound C)

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.refined_componentCenter_has_bound
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData} {n : ℕ}
    (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (hbound : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (n + 1) = ⊤)
    {Y : Scheme} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData}
    (e : Y ≅ GlobalBlowup.Data.Construction.globalBlowup A.center A.center_ne_bot)
    (hg : e.hom ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase A.center A.center_ne_bot ≫ f) = g)
    (hK : (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal A.center J A.center_ne_bot (n + 1)).comap e.hom = K)
    (B : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas g K n) : ∃ m, ∀ i, (B.choice i).HasBound m := by
  obtain ⟨C, _, m, hC⟩ := A.exists_bounded_atlas_after_component_blowup hbound
  exact ⟨m, C.hasBound_transport_etale B e.hom hg hK m hC⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
