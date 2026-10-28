import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GlobalFrame
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.CoordinateRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.FunctionFieldUnitGerm

/-! # Global Coordinate -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-! # LineBundleCycles: the actual rational coefficient of a line-bundle reference section in a global frame -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

instance Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.trivializingOpen_nonempty {X : Scheme.{0}} (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (x : X) :
    Nonempty (L.trivializingOpen x) := ⟨⟨x, L.mem_trivializingOpen x⟩⟩

variable {X : Scheme.{0}} [IsIntegral X] {L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X}
    (e : L.sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule X)

def LineBundle.GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient : X.functionFieldˣ :=
  FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm L.rationalReferenceOpen (LineBundle.GlobalFrame.Cycles.lineBundleGlobalFrameTransition e (genericPoint X) _ le_rfl)

theorem LineBundle.GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient_on_open (W : X.Opens) [Nonempty W]
    (hW : W ≤ L.rationalReferenceOpen) :
    LineBundle.GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e = FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W
      (LineBundle.GlobalFrame.Cycles.lineBundleGlobalFrameTransition e (genericPoint X) W hW) := by
  rw [← LineBundle.GlobalFrame.Cycles.lineBundleGlobalFrameTransition_restrict e (genericPoint X) hW le_rfl]
  exact (FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm_restrict hW _).symm

def LineBundle.GlobalCoordinate.Cycles.lineBundleGlobalLocalUnit (x : X) : Γ(X, L.trivializingOpen x)ˣ :=
  LineBundle.GlobalFrame.Cycles.lineBundleGlobalFrameTransition e x _ le_rfl

theorem LineBundle.GlobalCoordinate.Cycles.lineBundleGlobalLocalUnit_on_open (x : X) (W : X.Opens) [Nonempty W]
    (hW : W ≤ L.trivializingOpen x) :
    FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm (L.trivializingOpen x) (LineBundle.GlobalCoordinate.Cycles.lineBundleGlobalLocalUnit e x) =
      FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W (LineBundle.GlobalFrame.Cycles.lineBundleGlobalFrameTransition e x W hW) := by
  rw [← LineBundle.GlobalFrame.Cycles.lineBundleGlobalFrameTransition_restrict e x hW le_rfl]
  exact (FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm_restrict hW _).symm

theorem LineBundle.GlobalCoordinate.Cycles.lineBundleGlobal_coordinate_identity (x : X) :
    FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm (L.trivializingOpen x) (LineBundle.GlobalCoordinate.Cycles.lineBundleGlobalLocalUnit e x) *
      L.rationalSectionCoordinate x = LineBundle.GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e := by
  let W := L.rationalCoordinateDomain x
  rw [LineBundle.GlobalCoordinate.Cycles.lineBundleGlobalLocalUnit_on_open e x W inf_le_left,
    L.rationalSectionCoordinate_on_open x W le_rfl,
    LineBundle.GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient_on_open e W inf_le_right]
  change FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W _ * FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W _ = FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W _
  rw [← map_mul]
  exact congrArg (FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W)
    (LineBundle.GlobalFrame.Cycles.lineBundleGlobalFrameTransition_cocycle e x (genericPoint X) W inf_le_left inf_le_right)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
