import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitCechClasses
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.Add

/-! # Unit Cech Products -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitCechProducts

noncomputable section

/-! Products of actual normalized dual-number cocycles add their
classes in the original structure-sheaf cohomology. -/

open _root_.CategoryTheory _root_.TopologicalSpace

variable {X : TopCat.{0}} (R : TopCat.Sheaf CommRingCat.{0} X) {I : Type} (U : I → Opens X)

local instance dualProductClassGroup : AddCommGroup (CategoryTheory.Sheaf.H (UnitCechClasses.ringAdditiveSheaf R) 1) :=
  Cech.Add.cechClassAddCommGroup (UnitCechClasses.ringAdditiveSheaf R) 1

theorem dualUnitCechAdditive_product (u v w : UnitCechCoefficients.DualUnitCechCoefficients R.obj U)
    (hu : UnitCechCoefficients.DualUnitCechNormalized R.obj U u) (hv : UnitCechCoefficients.DualUnitCechNormalized R.obj U v)
    (hw : ∀ a, w a = u a * v a) :
    UnitCechCoefficients.dualUnitCechAdditive R.obj U w = UnitCechCoefficients.dualUnitCechAdditive R.obj U u + UnitCechCoefficients.dualUnitCechAdditive R.obj U v := by
  funext a
  exact (congrArg (fun x => x.val.snd) (hw a)).trans (UnitCoordinates.dualUnit_snd_mul (u a) (v a) (hu a) (hv a))

theorem dualUnitCechClass_product (hU : iSup U = ⊤) (u v w : UnitCechCoefficients.DualUnitCechCoefficients R.obj U)
    (hu : UnitCechCoefficients.DualUnitCechNormalized R.obj U u) (hv : UnitCechCoefficients.DualUnitCechNormalized R.obj U v)
    (hw : UnitCechCoefficients.DualUnitCechNormalized R.obj U w) (hcu : UnitCechCoefficients.DualUnitCechCocycle R.obj U u)
    (hcv : UnitCechCoefficients.DualUnitCechCocycle R.obj U v) (hcw : UnitCechCoefficients.DualUnitCechCocycle R.obj U w)
    (he : ∀ a, w a = u a * v a) :
    UnitCechClasses.dualUnitCechClass R U hU w hw hcw = UnitCechClasses.dualUnitCechClass R U hU u hu hcu + UnitCechClasses.dualUnitCechClass R U hU v hv hcv := by
  have hu' := UnitCechCoefficients.dualUnitCechAdditive_closed R.obj U u hu hcu
  have hv' := UnitCechCoefficients.dualUnitCechAdditive_closed R.obj U v hv hcv
  have hw' := UnitCechCoefficients.dualUnitCechAdditive_closed R.obj U w hw hcw
  exact (Cech.Add.cechSheafClass_congr U (UnitCechClasses.ringAdditiveSheaf R) hU 0 _ _ hw'
    (Cech.Add.cechAdd_closed U (UnitCechClasses.ringAdditiveSheaf R).obj 1 _ _ hu' hv')
    (dualUnitCechAdditive_product R U u v w hu hv he)).trans
      (Cech.Add.cechSheafClass_add U (UnitCechClasses.ringAdditiveSheaf R) hU 0 _ _ hu' hv')

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitCechProducts
