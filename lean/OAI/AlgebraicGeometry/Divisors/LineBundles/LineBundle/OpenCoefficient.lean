import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenFrames
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.CoordinateRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.FunctionFieldUnits

/-! # Open Coefficient -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-! # LineBundleCycles: the explicit rational coefficient comparing reference sections under open restriction -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)
    (i : Y ⟶ X) [IsOpenImmersion i]

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openReferenceDomain : Y.Opens :=
  i ⁻¹ᵁ L.rationalReferenceOpen ⊓ (L.restrictToOpen i).rationalReferenceOpen

instance Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openReferenceDomain_nonempty : Nonempty (L.openReferenceDomain i) :=
  ⟨⟨genericPoint Y, by
    constructor
    · change i (genericPoint Y) ∈ L.rationalReferenceOpen
      rw [genericPoint_eq_of_isOpenImmersion i]
      exact L.mem_trivializingOpen _
    · exact (L.restrictToOpen i).mem_trivializingOpen _⟩⟩

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openReferenceDomain_image : i ''ᵁ L.openReferenceDomain i ≤ L.rationalReferenceOpen := by
  rintro _ ⟨y, hy, rfl⟩
  exact hy.1

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openRationalCoefficient : Y.functionFieldˣ :=
  FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm (L.openReferenceDomain i)
    (L.openMixedTransitionOn i (genericPoint X) (genericPoint Y) _
      (L.openReferenceDomain_image i) inf_le_right)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openRationalCoefficient_on_open (W : Y.Opens) [Nonempty W]
    (hW : W ≤ L.openReferenceDomain i) :
    L.openRationalCoefficient i = FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W
      (L.openMixedTransitionOn i (genericPoint X) (genericPoint Y) W
        ((i.image_mono hW).trans (L.openReferenceDomain_image i)) (hW.trans inf_le_right)) := by
  rw [← L.openMixedTransitionOn_restrict i (genericPoint X) (genericPoint Y) hW
    (L.openReferenceDomain_image i) inf_le_right]
  exact (FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm_restrict hW _).symm

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openLocalDomain (x : Y) : Y.Opens :=
  i ⁻¹ᵁ L.trivializingOpen (i x) ⊓ (L.restrictToOpen i).trivializingOpen x

omit [IsIntegral X] [IsIntegral Y] in
theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.mem_openLocalDomain (x : Y) : x ∈ L.openLocalDomain i x :=
  ⟨L.mem_trivializingOpen (i x), (L.restrictToOpen i).mem_trivializingOpen x⟩

instance Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openLocalDomain_nonempty (x : Y) : Nonempty (L.openLocalDomain i x) :=
  ⟨⟨x, L.mem_openLocalDomain i x⟩⟩

omit [IsIntegral X] [IsIntegral Y] in
theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openLocalDomain_image (x : Y) : i ''ᵁ L.openLocalDomain i x ≤ L.trivializingOpen (i x) := by
  rintro _ ⟨y, hy, rfl⟩
  exact hy.1

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openLocalUnit (x : Y) : Γ(Y, L.openLocalDomain i x)ˣ :=
  L.openMixedTransitionOn i (i x) x _ (L.openLocalDomain_image i x) inf_le_right

omit [IsIntegral X] in
theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openLocalUnit_on_open (x : Y) (W : Y.Opens) [Nonempty W]
    (hW : W ≤ L.openLocalDomain i x) :
    FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm (L.openLocalDomain i x) (L.openLocalUnit i x) = FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W
      (L.openMixedTransitionOn i (i x) x W
        ((i.image_mono hW).trans (L.openLocalDomain_image i x)) (hW.trans inf_le_right)) := by
  rw [← L.openMixedTransitionOn_restrict i (i x) x hW (L.openLocalDomain_image i x) inf_le_right]
  exact (FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm_restrict hW _).symm

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionCoordinate_open_on_open (x : X) (W : Y.Opens) [Nonempty W]
    (hW : i ''ᵁ W ≤ L.rationalCoordinateDomain x) :
    Open.FunctionFieldUnits.BundleCycles.openFunctionFieldUnits i (L.rationalSectionCoordinate x) = FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W
      (Units.map (i.appIso W).hom.hom.toMonoidHom
        (L.ambientTransitionOn x (genericPoint X) (i ''ᵁ W)
          (hW.trans inf_le_left) (hW.trans inf_le_right))) := by
  rw [L.rationalSectionCoordinate_on_open x (i ''ᵁ W) hW]
  exact Open.FunctionFieldUnits.BundleCycles.openFunctionFieldUnits_germ i W _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
