import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.DominantCoefficientOnReference
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GenericCoefficientGlobalFrame

/-! # Dominant Global Frame -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.DominantGlobalFrame.Cycles

noncomputable section

/-! # LineBundleCycles: the actual pulled rational section is ordinary scalar pullback in every global frame -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y) {L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y}
    (e : L.sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule Y)

theorem dominantPullbackReferenceCoefficient_globalFrame :
    L.dominantPullbackReferenceCoefficient f hη *
        GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient (PullbackIso.Cycles.lineBundlePullbackGlobalTrivialization e f) =
      Units.map (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toMonoidHom (GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e) := by
  let U := L.rationalReferenceOpen
  let := DominantReferencePullback.Cycles.genericPointMap_preimage_nonempty f hη U
  let s := L.referenceSection
  let ep : (L.pullback f).sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule X := PullbackIso.Cycles.lineBundlePullbackGlobalTrivialization e f
  have hb : Y.germToFunctionField U (GlobalFrame.Cycles.lineBundleGlobalFrame e U s) = (GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e).val := by
    have h := GenericCoefficientGlobalFrame.Cycles.genericSectionCoefficient_globalFrame e U s
    rw [L.referenceSection_genericCoefficient, mul_one] at h
    exact h
  have hp := Module.PullbackUnitSections.BundleCycles.lineBundlePullbackGlobalTrivialization_section f e U s
  have hc := GenericCoefficientGlobalFrame.Cycles.genericSectionCoefficient_globalFrame ep (f ⁻¹ᵁ U) (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf U s)
  have hg := ConcreteCategory.congr_hom (Deformation.FunctionField.BundleCycles.genericFieldMap_germOn f hη U) (GlobalFrame.Cycles.lineBundleGlobalFrame e U s)
  apply Units.ext
  calc
    _ = (GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient ep).val * (L.dominantPullbackReferenceCoefficient f hη).val := mul_comm _ _
    _ = X.germToFunctionField (f ⁻¹ᵁ U)
        (GlobalFrame.Cycles.lineBundleGlobalFrame ep (f ⁻¹ᵁ U) (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf U s)) := hc.symm
    _ = X.germToFunctionField (f ⁻¹ᵁ U) (f.app U (GlobalFrame.Cycles.lineBundleGlobalFrame e U s)) :=
      congrArg (X.germToFunctionField (f ⁻¹ᵁ U)) hp
    _ = Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη (Y.germToFunctionField U (GlobalFrame.Cycles.lineBundleGlobalFrame e U s)) := hg.symm
    _ = _ := congrArg (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη) hb

theorem dominantPullbackSectionCoefficient_globalFrame (a : Y.functionFieldˣ) :
    L.dominantPullbackSectionCoefficient f hη a *
        GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient (PullbackIso.Cycles.lineBundlePullbackGlobalTrivialization e f) =
      Units.map (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toMonoidHom (a * GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e) := by
  unfold LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.dominantPullbackSectionCoefficient
  rw [mul_assoc, dominantPullbackReferenceCoefficient_globalFrame f hη e, map_mul]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.DominantGlobalFrame.Cycles
