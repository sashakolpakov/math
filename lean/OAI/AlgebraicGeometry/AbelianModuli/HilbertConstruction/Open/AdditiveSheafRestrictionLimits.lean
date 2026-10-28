import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictionCohomologyZero

/-! # Additive Sheaf Restriction Limits -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.AdditiveSheafRestrictionLimits.ZariskiCohomology.LocalKilling

noncomputable section

universe u
open _root_.CategoryTheory Limits Opposite _root_.TopologicalSpace _root_.AlgebraicGeometry

noncomputable instance openSheafPullback_preservesFiniteLimits
    {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteLimits (AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openSheafPullback U) := by
  let := U.ι.isOpenEmbedding.functor_isContinuous
  let E₁ := AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openSheafPullback U ⋙
    sheafToPresheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}
  let E₂ := sheafToPresheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj
      U.ι.isOpenEmbedding.functor.op
  let e : E₁ ≅ E₂ :=
    U.ι.isOpenEmbedding.functor.sheafPushforwardContinuousCompSheafToPresheafIso
      AddCommGrpCat.{u} (Opens.grothendieckTopology U)
        (Opens.grothendieckTopology X)
  have : PreservesFiniteLimits
      (sheafToPresheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}) := by infer_instance
  have : PreservesFiniteLimits
      ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj
        U.ι.isOpenEmbedding.functor.op) := by infer_instance
  have : PreservesFiniteLimits E₂ := by infer_instance
  have : PreservesFiniteLimits E₁ :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (sheafToPresheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u})

noncomputable instance openSheafPushforward_preservesFiniteLimits
    {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteLimits (AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openSheafPushforward U) := by
  let E₁ := AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openSheafPushforward U ⋙
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let E₂ := sheafToPresheaf
      (Opens.grothendieckTopology U) AddCommGrpCat.{u} ⋙
    TopCat.Presheaf.pushforward AddCommGrpCat.{u} U.ι.base
  let e : E₁ ≅ E₂ :=
    TopCat.Sheaf.pushforwardForgetIso AddCommGrpCat.{u} U.ι.base
  have : PreservesFiniteLimits
      (sheafToPresheaf (Opens.grothendieckTopology U)
        AddCommGrpCat.{u}) := by infer_instance
  have : PreservesFiniteLimits
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} U.ι.base) := by
    dsimp [TopCat.Presheaf.pushforward]
    exact ⟨fun J _ _ ↦ whiskeringLeft_preservesLimitsOfShape J _⟩
  have : PreservesFiniteLimits E₂ := by infer_instance
  have : PreservesFiniteLimits E₁ :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

noncomputable instance openRestrictionPushforward_preservesFiniteLimits
    {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteLimits (AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U) := by
  let : PreservesFiniteLimits
      (AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openSheafPullback U) :=
    openSheafPullback_preservesFiniteLimits U
  let : PreservesFiniteLimits
      (AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openSheafPushforward U) := by
    exact openSheafPushforward_preservesFiniteLimits U
  exact comp_preservesFiniteLimits _ _

theorem toSheaf_restrictAdjunction_unit
    {X : Scheme.{u}} (U : X.Opens) (M : X.Modules) :
    (SheafOfModules.toSheaf X.ringCatSheaf).map
        ((Scheme.Modules.restrictAdjunction U.ι).unit.app M) =
      (AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit U).app
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) := rfl

theorem zariskiFunctor_map_restrictAdjunction_unit_eq_zero
    {X : Scheme.{u}} {n : ℕ} (U : X.Opens) (M : X.Modules) (c : Zariski.Cohomology.ZariskiCohomology.H M n)
    (hc : (c.comp (Abelian.Ext.mk₀
      ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit U).app
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M))) rfl :
          AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.ExtH ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).obj
            ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) n) = 0) :
    (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor X n).map
      ((Scheme.Modules.restrictAdjunction U.ι).unit.app M) c = 0 := by
  exact hc

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.AdditiveSheafRestrictionLimits.ZariskiCohomology.LocalKilling
