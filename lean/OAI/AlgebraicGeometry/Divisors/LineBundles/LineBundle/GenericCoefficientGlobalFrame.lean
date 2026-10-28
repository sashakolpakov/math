import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RationalCoefficient
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GlobalCoordinate

/-! # Generic Coefficient Global Frame -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GenericCoefficientGlobalFrame.Cycles

noncomputable section

/-! # LineBundleCycles: actual global-frame coordinates of a local section determine its generic rational coefficient -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [IsIntegral X] {L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X}
    (e : L.sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule X)

theorem genericSectionCoefficient_globalFrame_on_reference (U : X.Opens) [Nonempty U]
    (hU : U ≤ L.rationalReferenceOpen) (s : Γ(L.sheaf, U)) :
    X.germToFunctionField U (GlobalFrame.Cycles.lineBundleGlobalFrame e U s) =
      (GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e).val * L.genericSectionCoefficient U s := by
  rw [L.genericSectionCoefficient_eq_local (genericPoint X) U hU]
  unfold LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.localRationalCoefficient
  rw [L.rationalSectionCoordinate_reference]
  simp only [Units.val_one, div_one]
  rw [GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient_on_open e U hU]
  change X.germToFunctionField U (GlobalFrame.Cycles.lineBundleGlobalFrame e U s) =
    X.germToFunctionField U (GlobalFrame.Cycles.lineBundleGlobalFrameTransition e (genericPoint X) U hU).val *
      X.germToFunctionField U (L.sectionFrame (genericPoint X) U hU s)
  rw [← map_mul]
  exact congrArg (X.germToFunctionField U)
    (FrameComparison.Cycles.LineBundleConstruction.frameTransitionUnit_coordinates (GlobalFrame.Cycles.lineBundleGlobalFrame e U)
      (L.sectionFrame (genericPoint X) U hU) s)

theorem genericSectionCoefficient_globalFrame (U : X.Opens) [Nonempty U] (s : Γ(L.sheaf, U)) :
    X.germToFunctionField U (GlobalFrame.Cycles.lineBundleGlobalFrame e U s) =
      (GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e).val * L.genericSectionCoefficient U s := by
  let V := L.genericCoefficientDomain U
  have hVU : V ≤ U := inf_le_left
  have H := congrArg (X.germToFunctionField V) (GlobalFrame.Cycles.lineBundleGlobalFrame_naturality e hVU s)
  calc
    X.germToFunctionField U (GlobalFrame.Cycles.lineBundleGlobalFrame e U s) =
        X.germToFunctionField V (GlobalFrame.Cycles.lineBundleGlobalFrame e V (L.sheaf.presheaf.map (homOfLE hVU).op s)) :=
      (H.trans (RationalBoundary.BundleCycles.RationalUnitRepresentative.germ_restrict hVU (GlobalFrame.Cycles.lineBundleGlobalFrame e U s))).symm
    _ = (GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e).val *
        L.genericSectionCoefficient V (L.sheaf.presheaf.map (homOfLE hVU).op s) :=
      genericSectionCoefficient_globalFrame_on_reference e V inf_le_right _
    _ = _ := congrArg (fun z => (GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e).val * z)
      (L.genericSectionCoefficient_restrict hVU s)

omit [IsIntegral X] in
theorem lineBundleGlobalFrame_isUnit_of_localFrame (x : X) (U : X.Opens)
    (hU : U ≤ L.trivializingOpen x) (s : Γ(L.sheaf, U)) (hs : IsUnit (L.sectionFrame x U hU s)) :
    IsUnit (GlobalFrame.Cycles.lineBundleGlobalFrame e U s) := by
  have H : GlobalFrame.Cycles.lineBundleGlobalFrame e U s = (GlobalFrame.Cycles.lineBundleGlobalFrameTransition e x U hU).val * L.sectionFrame x U hU s :=
    FrameComparison.Cycles.LineBundleConstruction.frameTransitionUnit_coordinates _ _ _
  rw [H]
  exact (GlobalFrame.Cycles.lineBundleGlobalFrameTransition e x U hU).isUnit.mul hs

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GenericCoefficientGlobalFrame.Cycles
