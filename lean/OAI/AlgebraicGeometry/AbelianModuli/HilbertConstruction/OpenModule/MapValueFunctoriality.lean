import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapComposition

/-! # Map Value Functoriality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapValueFunctoriality

noncomputable section

/-! Functoriality of actual module-map values on common ambient opens.
These identities turn ordinary overlap isomorphisms into the section
transition data used by effective module-object gluing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {X Y Z : Scheme.{u}}

theorem openModuleMapValue_identity (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (U : X.Opens) (hU : U ≤ f.opensRange) (s : Γ(M, U)) :
    MapValues.openModuleMapValue f (𝟙 (M.restrict f)) U hU s = s := by
  let := MapValues.moduleRestrictionUnit_app_isIso f M U hU
  apply (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.restrictAdjunction f).unit.app M).app U)).injective
  have h : (Scheme.Modules.restrictAdjunction f).unit.app M ≫
      (Scheme.Modules.pushforward f).map (𝟙 (M.restrict f)) =
        (Scheme.Modules.restrictAdjunction f).unit.app M := by
    rw [(Scheme.Modules.pushforward f).map_id]
    exact Category.comp_id _
  exact (MapRecovery.openModuleMapValue_spec f (𝟙 (M.restrict f)) U hU s).trans
    (congrArg (fun a => a.app U s) h)

theorem openModuleMapValue_hom_comp (f : Y ⟶ X) [IsOpenImmersion f]
    {M N P : X.Modules} (a : M.restrict f ⟶ N.restrict f)
    (b : N.restrict f ⟶ P.restrict f) (U : X.Opens) (hU : U ≤ f.opensRange)
    (s : Γ(M, U)) :
    MapValues.openModuleMapValue f (a ≫ b) U hU s =
      MapValues.openModuleMapValue f b U hU (MapValues.openModuleMapValue f a U hU s) := by
  let := MapValues.moduleRestrictionUnit_app_isIso f P U hU
  apply (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.restrictAdjunction f).unit.app P).app U)).injective
  rw [MapRecovery.openModuleMapValue_spec, MapRecovery.openModuleMapValue_spec]
  change b.app (f ⁻¹ᵁ U)
      (a.app (f ⁻¹ᵁ U) (((Scheme.Modules.restrictAdjunction f).unit.app M).app U s)) =
    b.app (f ⁻¹ᵁ U)
      (((Scheme.Modules.restrictAdjunction f).unit.app N).app U
        (MapValues.openModuleMapValue f a U hU s))
  exact congrArg (b.app (f ⁻¹ᵁ U)) (MapRecovery.openModuleMapValue_spec f a U hU s).symm

private theorem restrictFunctorCongr_refl (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) :
    (Scheme.Modules.restrictFunctorCongr (rfl : f = f)).app M = Iso.refl (M.restrict f) := by
  apply Iso.ext
  apply Scheme.Modules.hom_ext
  intro U
  simp only [Iso.app_hom, Scheme.Modules.restrictFunctorCongr_hom_app_app,
    eqToHom_refl, op_id, Iso.refl_hom, Scheme.Modules.Hom.id_app]
  exact M.presheaf.map_id _

def openModuleMapCongr (f g : Y ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (h : f = g) {M N : X.Modules} (a : M.restrict f ⟶ N.restrict f) :
    M.restrict g ⟶ N.restrict g :=
  (Scheme.Modules.restrictFunctorCongr h).inv.app M ≫ a ≫
    (Scheme.Modules.restrictFunctorCongr h).hom.app N

theorem openModuleMapValue_congr (f g : Y ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (h : f = g) {M N : X.Modules} (a : M.restrict f ⟶ N.restrict f)
    (U : X.Opens) (hf : U ≤ f.opensRange) (hg : U ≤ g.opensRange) (s : Γ(M, U)) :
    MapValues.openModuleMapValue g (openModuleMapCongr f g h a) U hg s = MapValues.openModuleMapValue f a U hf s := by
  subst g
  have hM := restrictFunctorCongr_refl f M
  have hN := restrictFunctorCongr_refl f N
  change MapValues.openModuleMapValue f
    (((Scheme.Modules.restrictFunctorCongr rfl).app M).inv ≫ a ≫
      ((Scheme.Modules.restrictFunctorCongr rfl).app N).hom) U hg s = _
  rw [hM, hN, Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id]

def restrictOpenModuleMapTo (f : Z ⟶ Y) (g : Y ⟶ X) (q : Z ⟶ X)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion q]
    (h : f ≫ g = q) {M N : X.Modules} (a : M.restrict g ⟶ N.restrict g) :
    M.restrict q ⟶ N.restrict q :=
  openModuleMapCongr (f ≫ g) q h (MapComposition.restrictOpenModuleMap f g a)

theorem restrictOpenModuleMapTo_value (f : Z ⟶ Y) (g : Y ⟶ X) (q : Z ⟶ X)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion q]
    (h : f ≫ g = q) {M N : X.Modules} (a : M.restrict g ⟶ N.restrict g)
    (U : X.Opens) (hq : U ≤ q.opensRange) (hg : U ≤ g.opensRange) (s : Γ(M, U)) :
    MapValues.openModuleMapValue q (restrictOpenModuleMapTo f g q h a) U hq s =
      MapValues.openModuleMapValue g a U hg s := by
  have hfg : U ≤ (f ≫ g).opensRange := by simpa only [h] using hq
  exact (openModuleMapValue_congr (f ≫ g) q h (MapComposition.restrictOpenModuleMap f g a) U hfg hq s).trans
    (LinearMap.congr_fun (MapComposition.openModuleMapValue_comp f g a U hfg) s)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapValueFunctoriality
