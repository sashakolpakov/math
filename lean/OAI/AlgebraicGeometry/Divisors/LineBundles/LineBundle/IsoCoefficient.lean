import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.IsoFrames
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.CoordinateRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.FunctionFieldUnitGerm

/-! # Iso Coefficient -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.IsoCoefficient.Cycles

noncomputable section

section

/-! # LineBundleCycles: the genuine rational coefficient relating reference sections through a sheaf isomorphism -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [IsIntegral X] {L M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X} (e : L.sheaf ≅ M.sheaf)

def lineBundleIsoReferenceOpen (L M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) : X.Opens :=
  L.rationalReferenceOpen ⊓ M.rationalReferenceOpen

instance lineBundleIsoReferenceOpen_nonempty : Nonempty (lineBundleIsoReferenceOpen L M) :=
  ⟨⟨genericPoint X, L.mem_trivializingOpen _, M.mem_trivializingOpen _⟩⟩

def lineBundleIsoRationalCoefficient : X.functionFieldˣ :=
  FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm (lineBundleIsoReferenceOpen L M)
    (IsoFrames.Cycles.lineBundleIsoTransition e (genericPoint X) (genericPoint X) _ inf_le_left inf_le_right)

theorem lineBundleIsoRationalCoefficient_on_open (W : X.Opens) [Nonempty W]
    (hW : W ≤ lineBundleIsoReferenceOpen L M) :
    lineBundleIsoRationalCoefficient e = FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W
      (IsoFrames.Cycles.lineBundleIsoTransition e (genericPoint X) (genericPoint X) W
        (hW.trans inf_le_left) (hW.trans inf_le_right)) := by
  rw [← IsoFrames.Cycles.lineBundleIsoTransition_restrict e (genericPoint X) (genericPoint X) hW inf_le_left inf_le_right]
  exact (FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm_restrict hW _).symm

def lineBundleIsoLocalOpen (L M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (x : X) : X.Opens :=
  L.trivializingOpen x ⊓ M.trivializingOpen x

instance lineBundleIsoLocalOpen_nonempty (x : X) : Nonempty (lineBundleIsoLocalOpen L M x) :=
  ⟨⟨x, L.mem_trivializingOpen x, M.mem_trivializingOpen x⟩⟩

def lineBundleIsoLocalUnit (x : X) : Γ(X, lineBundleIsoLocalOpen L M x)ˣ :=
  IsoFrames.Cycles.lineBundleIsoTransition e x x _ inf_le_left inf_le_right

theorem lineBundleIsoLocalUnit_on_open (x : X) (W : X.Opens) [Nonempty W]
    (hW : W ≤ lineBundleIsoLocalOpen L M x) :
    FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm (lineBundleIsoLocalOpen L M x) (lineBundleIsoLocalUnit e x) =
      FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W (IsoFrames.Cycles.lineBundleIsoTransition e x x W
        (hW.trans inf_le_left) (hW.trans inf_le_right)) := by
  rw [← IsoFrames.Cycles.lineBundleIsoTransition_restrict e x x hW inf_le_left inf_le_right]
  exact (FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm_restrict hW _).symm

theorem lineBundleIsoLocalUnit_order [IsLocallyNoetherian X] (x : X) :
    X.ord (FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm (lineBundleIsoLocalOpen L M x) (lineBundleIsoLocalUnit e x)).val x = 0 :=
  FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm_order _ _ x ⟨L.mem_trivializingOpen x, M.mem_trivializingOpen x⟩

end

/-! # LineBundleCycles: actual rational-section coordinates under a genuine line-bundle isomorphism -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem lineBundleIso_coordinate_identity {X : Scheme.{0}} [IsIntegral X]
    {L M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X} (e : L.sheaf ≅ M.sheaf) (x : X) :
    M.rationalSectionCoordinate x * lineBundleIsoRationalCoefficient e =
      FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm (lineBundleIsoLocalOpen L M x) (lineBundleIsoLocalUnit e x) *
        L.rationalSectionCoordinate x := by
  let W := lineBundleIsoLocalOpen L M x ⊓ lineBundleIsoReferenceOpen L M
  have : Nonempty W := ⟨⟨genericPoint X,
    ⟨L.genericPoint_mem_trivializingOpen x, M.genericPoint_mem_trivializingOpen x⟩,
    ⟨L.mem_trivializingOpen _, M.mem_trivializingOpen _⟩⟩⟩
  have hL : W ≤ L.rationalCoordinateDomain x :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have hM : W ≤ M.rationalCoordinateDomain x :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  rw [M.rationalSectionCoordinate_on_open x W hM, L.rationalSectionCoordinate_on_open x W hL,
    lineBundleIsoRationalCoefficient_on_open e W inf_le_right,
    lineBundleIsoLocalUnit_on_open e x W inf_le_left]
  change FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W _ * FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W _ =
    FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W _ * FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W _
  rw [← map_mul, ← map_mul]
  exact congrArg (FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W)
    (IsoFrames.Cycles.lineBundleIsoTransition_four e x (genericPoint X) x (genericPoint X) W
      (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
      (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.IsoCoefficient.Cycles
