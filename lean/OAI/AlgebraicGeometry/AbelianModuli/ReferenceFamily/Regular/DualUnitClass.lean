import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitCechClassification
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.TermModules
import OAI.AlgebraicGeometry.SheafCohomology.AffineH

/-! # Dual Unit Class -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.DualUnitClass

noncomputable section

/-! Normalized regular dual-number cocycles define classes in the
original algebraic structure-sheaf H1, with exact frame-change detection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens)

def regularDualUnitClass (hU : iSup U = ⊤) (u : Dual.UnitCechCoefficients.DualUnitCechCoefficients X.sheaf.obj U)
    (hu : Dual.UnitCechCoefficients.DualUnitCechNormalized X.sheaf.obj U u) (hc : Dual.UnitCechCoefficients.DualUnitCechCocycle X.sheaf.obj U u) :
    SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule X) 1 :=
  Dual.UnitCechClasses.dualUnitCechClass X.sheaf U hU u hu hc

theorem regularDualUnitClass_eq_iff_gauge (hU : iSup U = ⊤)
    (u v : Dual.UnitCechCoefficients.DualUnitCechCoefficients X.sheaf.obj U)
    (hu : Dual.UnitCechCoefficients.DualUnitCechNormalized X.sheaf.obj U u) (hv : Dual.UnitCechCoefficients.DualUnitCechNormalized X.sheaf.obj U v)
    (hcu : Dual.UnitCechCoefficients.DualUnitCechCocycle X.sheaf.obj U u) (hcv : Dual.UnitCechCoefficients.DualUnitCechCocycle X.sheaf.obj U v) :
    regularDualUnitClass X U hU v hv hcv = regularDualUnitClass X U hU u hu hcu ↔
    ∃ g : ∀ i, (DualNumber Γ(X, U i))ˣ,
      (∀ i, (g i).val.fst = 1) ∧ ∀ a : Fin 2 → I, v a = u a *
        Dual.UnitCechCoefficients.dualCechRestrict X.sheaf.obj (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1) (g (a 1)) /
        Dual.UnitCechCoefficients.dualCechRestrict X.sheaf.obj (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0) (g (a 0)) :=
  Dual.UnitCechClassification.dualUnitCechClass_eq_iff_gauge X.sheaf U hU u v hu hv hcu hcv

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.DualUnitClass
