import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.TensorCompositionUnits

/-! # Unit Composite Injectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.UnitCompositeInjectivity

noncomputable section

/-! Injectivity of the composite pullback unit on global sections implies injectivity of the first pullback unit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem pullbackUnit_top_injective_of_composite
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (h : Function.Injective (((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app ⊤)) :
    Function.Injective (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app ⊤) := by
  let η := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M
  let β := (Scheme.Modules.pushforward g).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app ((Scheme.Modules.pullback g).obj M)) ≫
    (Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.pullbackComp f g).hom.app M)) ≫
    (Scheme.Modules.pushforwardComp f g).hom.app ((Scheme.Modules.pullback (f ≫ g)).obj M)
  have he : η ≫ β = (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M :=
    TensorCompositionUnits.pullbackComp_hom_unit f g M
  intro s t hst
  apply h
  exact (ConcreteCategory.congr_hom (congrArg (fun a => a.app ⊤) he) s).symm.trans
    ((congrArg (β.app ⊤) hst).trans
      (ConcreteCategory.congr_hom (congrArg (fun a => a.app ⊤) he) t))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.UnitCompositeInjectivity
