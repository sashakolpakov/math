import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.AdditiveSheafRestriction

/-! # Restriction Cohomology Zero -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictionCohomologyZero.ZariskiCohomology.LocalKilling

noncomputable section

universe u
open _root_.CategoryTheory Limits Opposite _root_.TopologicalSpace _root_.AlgebraicGeometry

noncomputable def openRestrictionPushforwardHZeroOfSection
    {X : Scheme.{u}} (U : X.Opens) (F : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf X)
    (t : F.1.obj (op U)) :
    AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.ExtH ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).obj F) 0 :=
  (CategoryTheory.Sheaf.H.equiv₀
    ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).obj F)
    (isTerminalTop : IsTerminal (⊤ : Opens X))).symm
      (AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforwardSection U F t)

theorem openRestrictionPushforwardHZeroOfSection_map
    {X : Scheme.{u}} (U : X.Opens) {F G : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf X}
    (f : F ⟶ G) (t : F.1.obj (op U)) :
    (openRestrictionPushforwardHZeroOfSection U F t).comp
        (Abelian.Ext.mk₀ ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).map f)) rfl =
      openRestrictionPushforwardHZeroOfSection U G
        (f.hom.app (op U) t) := by
  change CategoryTheory.Sheaf.H.map
      ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).map f) 0
        (openRestrictionPushforwardHZeroOfSection U F t) = _
  apply (CategoryTheory.Sheaf.H.equiv₀
    ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).obj G)
    (isTerminalTop : IsTerminal (⊤ : Opens X))).injective
  rw [← CategoryTheory.Sheaf.H.equiv₀_naturality]
  dsimp [openRestrictionPushforwardHZeroOfSection]
  simp only [AddEquiv.apply_symm_apply]
  exact AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforwardSection_map U f t

theorem openRestrictionPushforwardUnit_HZero
    {X : Scheme.{u}} (U : X.Opens) (F : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf X)
    (q : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.ExtH F 0) :
    q.comp (Abelian.Ext.mk₀
        ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit U).app F)) rfl =
      openRestrictionPushforwardHZeroOfSection U F
        (F.1.map (homOfLE le_top).op
          (CategoryTheory.Sheaf.H.equiv₀ F
            (isTerminalTop : IsTerminal (⊤ : Opens X)) q)) := by
  change CategoryTheory.Sheaf.H.map
      ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit U).app F) 0 q = _
  apply (CategoryTheory.Sheaf.H.equiv₀
    ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).obj F)
    (isTerminalTop : IsTerminal (⊤ : Opens X))).injective
  rw [← CategoryTheory.Sheaf.H.equiv₀_naturality]
  dsimp [openRestrictionPushforwardHZeroOfSection]
  rw [AddEquiv.apply_symm_apply]
  exact AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit_section U F _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictionCohomologyZero.ZariskiCohomology.LocalKilling
