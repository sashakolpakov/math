import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenCoefficient

/-! # Open Coordinate Identity -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-! # LineBundleCycles: the actual coordinate identity for a line bundle restricted along an open immersion -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)
    (i : Y ⟶ X) [IsOpenImmersion i]

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.open_coordinate_identity (x : Y) :
    FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm (L.openLocalDomain i x) (L.openLocalUnit i x) *
      (L.restrictToOpen i).rationalSectionCoordinate x =
    Open.FunctionFieldUnits.BundleCycles.openFunctionFieldUnits i (L.rationalSectionCoordinate (i x)) * L.openRationalCoefficient i := by
  let W := L.openLocalDomain i x ⊓ L.openReferenceDomain i
  have : Nonempty W := by
    refine ⟨⟨genericPoint Y, ?_, ?_⟩⟩
    · exact ((genericPoint_spec Y).mem_open_set_iff (L.openLocalDomain i x).isOpen).mpr
        ⟨x, Set.mem_univ x, L.mem_openLocalDomain i x⟩
    · exact ((genericPoint_spec Y).mem_open_set_iff (L.openReferenceDomain i).isOpen).mpr
        (by simpa using (show Nonempty (L.openReferenceDomain i) from inferInstance))
  have hW : i ''ᵁ W ≤ L.rationalCoordinateDomain (i x) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨hy.1.1, hy.2.1⟩
  have hM : W ≤ (L.restrictToOpen i).rationalCoordinateDomain x :=
    fun _ hy => ⟨hy.1.2, hy.2.2⟩
  rw [L.openLocalUnit_on_open i x W inf_le_left,
    (L.restrictToOpen i).rationalSectionCoordinate_on_open x W hM,
    L.rationalSectionCoordinate_open_on_open i (i x) W hW,
    L.openRationalCoefficient_on_open i W inf_le_right]
  change FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W _ * FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W _ =
    FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W _ * FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W _
  rw [← map_mul, ← map_mul]
  exact congrArg (FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm W)
    (L.openMixedTransitionOn_square i (i x) (genericPoint X) x (genericPoint Y) W
      (hW.trans inf_le_left) (hW.trans inf_le_right) (hM.trans inf_le_left) (hM.trans inf_le_right))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
