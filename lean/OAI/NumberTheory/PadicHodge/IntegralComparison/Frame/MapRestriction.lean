import OAI.AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates

/-! # Map Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.MapRestriction

noncomputable section

/-! A map between genuine rank-one frames acts on every smaller open by
the restriction of its coefficient on the original open. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates

universe u

variable {X : Scheme.{u}} {M N : X.Modules} (U : X.Opens)
  (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
  (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (f : M ⟶ N)

theorem conjugated_eq_scalar :
    eM.inv ≫ f.over U ≫ eN.hom =
      AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U
        (AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameMapCoefficient U eM eN f) := by
  have h := (AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U).symm_apply_apply
    (eM.inv ≫ f.over U ≫ eN.hom)
  exact h.symm

theorem framed_eq_scalar :
    f.over U ≫ eN.hom = eM.hom ≫
      AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U
        (AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameMapCoefficient U eM eN f) := by
  have h := congrArg (fun g => eM.hom ≫ g) (conjugated_eq_scalar U eM eN f)
  simpa only [Iso.hom_inv_id_assoc] using h

theorem coordinate_on_subopen {V : X.Opens} (h : V ≤ U) (x : Γ(M, V)) :
    (AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameSectionEquiv N V
      (AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf N U eN
        (Over.mk (homOfLE h)))).symm (f.app V x) =
    X.presheaf.map (homOfLE h).op (AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameMapCoefficient U eM eN f) *
      (AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameSectionEquiv M V
        (AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U eM
          (Over.mk (homOfLE h)))).symm x := by
  have he := congrArg (fun g => g.val.app (op (Over.mk (homOfLE h))))
    (framed_eq_scalar U eM eN f)
  have hx := ConcreteCategory.congr_hom he x
  change eN.hom.val.app (op (Over.mk (homOfLE h))) (f.app V x) =
    (AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U
      (AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameMapCoefficient U eM eN f)).val.app (op (Over.mk (homOfLE h)))
        (eM.hom.val.app (op (Over.mk (homOfLE h))) x) at hx
  rw [AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd_app_apply] at hx
  change eN.hom.val.app (op (Over.mk (homOfLE h))) (f.app V x) =
    (show Γ(X, V) from eM.hom.val.app (op (Over.mk (homOfLE h))) x) *
      X.presheaf.map (homOfLE h).op (AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameMapCoefficient U eM eN f) at hx
  calc
    _ = (show Γ(X, V) from eM.hom.val.app (op (Over.mk (homOfLE h))) x) *
        X.presheaf.map (homOfLE h).op (AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameMapCoefficient U eM eN f) := hx
    _ = X.presheaf.map (homOfLE h).op (AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameMapCoefficient U eM eN f) *
        (show Γ(X, V) from eM.hom.val.app (op (Over.mk (homOfLE h))) x) :=
      mul_comm (show Γ(X, V) from eM.hom.val.app (op (Over.mk (homOfLE h))) x)
        (X.presheaf.map (homOfLE h).op (AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameMapCoefficient U eM eN f))
    _ = _ := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.MapRestriction
