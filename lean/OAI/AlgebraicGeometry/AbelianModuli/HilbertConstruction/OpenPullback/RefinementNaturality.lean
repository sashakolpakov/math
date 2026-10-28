import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.Refinement

/-! # Refinement Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.RefinementNaturality

noncomputable section

/-! Refining a canonical open pullback preserves the ambient values of every local module map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [IsOpenImmersion f] [IsOpenImmersion g] {M N : Z.Modules}
variable (φ : (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback g).obj N)

omit [IsOpenImmersion f] [IsOpenImmersion g] in
theorem openPullbackRefinementMap_natural :
    (Scheme.Modules.pushforward g).map φ ≫ Refinement.openPullbackRefinementMap f g N =
      Refinement.openPullbackRefinementMap f g M ≫
        (Scheme.Modules.pushforward (f ≫ g)).map (Refinement.refineOpenPullbackMap f g φ) := by
  have he : (Scheme.Modules.pullbackComp f g).hom.app M ≫ Refinement.refineOpenPullbackMap f g φ =
      (Scheme.Modules.pullback f).map φ ≫ (Scheme.Modules.pullbackComp f g).hom.app N := by
    exact ((Scheme.Modules.pullbackComp f g).app M).hom_inv_id_assoc _
  have hn : (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app ((Scheme.Modules.pullback g).obj M) ≫
      (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map φ) =
      φ ≫ (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app ((Scheme.Modules.pullback g).obj N) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality φ).symm
  symm
  dsimp only [Refinement.openPullbackRefinementMap]
  simp only [Category.assoc]
  rw [← (Scheme.Modules.pushforwardComp f g).hom.naturality (Refinement.refineOpenPullbackMap f g φ)]
  change (Scheme.Modules.pushforward g).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app ((Scheme.Modules.pullback g).obj M)) ≫
    (Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.pullbackComp f g).hom.app M)) ≫
    (Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward f).map (Refinement.refineOpenPullbackMap f g φ)) ≫ _ = _
  rw [← Category.assoc ((Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward f).map
    ((Scheme.Modules.pullbackComp f g).hom.app M))), ← Functor.map_comp, ← Functor.map_comp, he]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pushforward g).map
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app ((Scheme.Modules.pullback g).obj M))),
    ← Functor.map_comp, hn,
    Functor.map_comp, Category.assoc]

theorem openPullbackModuleValue_comp (U : Z.Opens) (hU : U ≤ (f ≫ g).opensRange) :
    ModuleValues.openPullbackModuleValue (f ≫ g) (Refinement.refineOpenPullbackMap f g φ) U hU =
      ModuleValues.openPullbackModuleValue g φ U (hU.trans (by
        rw [Scheme.Hom.opensRange_comp]
        exact g.image_le_opensRange f.opensRange)) := by
  have hg : U ≤ g.opensRange := hU.trans (by
    rw [Scheme.Hom.opensRange_comp]
    exact g.image_le_opensRange f.opensRange)
  let := ModuleValues.openPullbackUnit_app_isIso g N U hg
  let := ModuleValues.openPullbackUnit_app_isIso (f ≫ g) N U hU
  have hα : ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M ≫
      (Scheme.Modules.pushforward g).map φ) ≫ Refinement.openPullbackRefinementMap f g N =
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M ≫
        (Scheme.Modules.pushforward (f ≫ g)).map (Refinement.refineOpenPullbackMap f g φ) := by
    rw [Category.assoc, openPullbackRefinementMap_natural, ← Category.assoc,
      Refinement.openPullbackRefinementMap_unit]
  exact (Module.MapFactorTransport.moduleMapLocalFactor_transport _ _ (Refinement.openPullbackRefinementMap f g N) _ _ hα
    (Refinement.openPullbackRefinementMap_unit f g N) U).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.RefinementNaturality
