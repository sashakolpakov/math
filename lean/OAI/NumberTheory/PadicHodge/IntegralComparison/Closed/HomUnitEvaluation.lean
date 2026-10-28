import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.InternalHom
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.HomUnitEvaluation

/-! # Hom Unit Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.HomUnitEvaluation

noncomputable section

/-! Closed direct image commutes with literal evaluation at the
structure-sheaf unit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
  (M N : X.Modules) [M.IsQuasicoherent]
  (v : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X ⟶ M)

def unit : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y ⟶ (Scheme.Modules.pushforward i).obj M :=
  SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom ≫ (Scheme.Modules.pushforward i).map v

omit [IsClosedImmersion i] [M.IsQuasicoherent] in
theorem unit_one (U : Y.Opens) : (unit i M v).app U (1 : Γ(Y, U)) =
    v.app (i ⁻¹ᵁ U) (1 : Γ(X, i ⁻¹ᵁ U)) := by
  change v.app (i ⁻¹ᵁ U) ((i.app U).hom 1) = _
  rw [map_one]

theorem normalization :
    (InternalHom.iso i M N).hom ≫
      Sheaf.HomUnitEvaluation.map ((Scheme.Modules.pushforward i).obj M)
        ((Scheme.Modules.pushforward i).obj N) (unit i M v) =
      (Scheme.Modules.pushforward i).map (Sheaf.HomUnitEvaluation.map M N v) := by
  apply AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.BasisIsomorphisms.moduleMap_eq_of_basis
    (Principal.BasisGluing.opens (fun _ => True))
    (Principal.BasisGluing.isBasis (fun _ => True) InternalHom.affine_neighborhood)
  intro U
  apply ConcreteCategory.hom_ext
  intro z
  change (Sheaf.HomUnitEvaluation.map _ _ (unit i M v)).app U.val
    ((InternalHom.iso i M N).hom.app U.val z) =
      (Sheaf.HomUnitEvaluation.map M N v).app (i ⁻¹ᵁ U.val) z
  rw [Sheaf.HomUnitEvaluation.app, unit_one, InternalHom.iso_app i M N U.val U.property.1,
    InternalHom.evaluation, Sheaf.HomUnitEvaluation.app]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.HomUnitEvaluation
