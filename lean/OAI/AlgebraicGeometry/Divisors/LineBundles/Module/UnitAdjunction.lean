import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SchemeIdealModule

/-! # Unit Adjunction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Module.UnitAdjunction.BundleCycles

noncomputable section

/-! The actual structure-module pullback isomorphism is adjoint
to the genuine map on regular functions. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

theorem schemeStructurePushforwardMap_eq_native :
    LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeStructurePushforwardMap f = SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  exact LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeStructurePushforwardMap_apply f U a

theorem modulePullbackUnitIso_adjunction :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (LineBundle.OpenRestriction.Cycles.modulePullbackUnitIso f).hom =
      LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeStructurePushforwardMap f := by
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs ((Scheme.Modules.pushforward f).IsRightAdjoint)
  change (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).homEquiv _ _
    (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) = _
  exact (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit f.toRingCatSheafHom).trans
    (schemeStructurePushforwardMap_eq_native f).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Module.UnitAdjunction.BundleCycles
