import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.TensorCompositionUnits

/-! # Unit Composition Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.UnitCompositionValues

noncomputable section

/-! The canonical pullback-composition isomorphism identifies successive pullbacks of actual section values with their composite pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem pullbackUnit_comp_value {X Y Z : Scheme.{u}} (a : Z ⟶ Y) (j : Y ⟶ X)
    (M : X.Modules) (U : X.Opens) (x : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp a j).hom.app M).app ((a ≫ j) ⁻¹ᵁ U)
      ((((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app ((Scheme.Modules.pullback j).obj M)).app (j ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).app U x)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (a ≫ j)).unit.app M).app U x :=
  congrArg (fun z : M ⟶ (Scheme.Modules.pushforward (a ≫ j)).obj ((Scheme.Modules.pullback (a ≫ j)).obj M) =>
    z.app U x) (TensorCompositionUnits.pullbackComp_hom_unit a j M)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.UnitCompositionValues
