import OAI.AlgebraicGeometry.Divisors.LineBundles.Module.PullbackUnitSections
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GlobalFrame
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RationalCoefficient

/-! # Pullback Generator -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.PullbackGenerator.Cycles

noncomputable section

/-! # LineBundleCycles: an actual local generator remains nonzero under arbitrary pullback to a nonempty open -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y)
    (e : L.sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule Y)

theorem lineBundlePullbackSection_ne_zero (U : Y.Opens) [Nonempty (f ⁻¹ᵁ U)]
    (s : Γ(L.sheaf, U)) (hs : IsUnit (GlobalFrame.Cycles.lineBundleGlobalFrame e U s)) :
    Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf U s ≠ 0 := by
  intro hzero
  have he := Module.PullbackUnitSections.BundleCycles.lineBundlePullbackGlobalTrivialization_section f e U s
  have hz : (PullbackIso.Cycles.lineBundlePullbackGlobalTrivialization e f).hom.app (f ⁻¹ᵁ U)
      (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf U s) = 0 :=
    (congrArg (fun z => (PullbackIso.Cycles.lineBundlePullbackGlobalTrivialization e f).hom.app (f ⁻¹ᵁ U) z) hzero).trans
      ((PullbackIso.Cycles.lineBundlePullbackGlobalTrivialization e f).hom.app (f ⁻¹ᵁ U)).hom.map_zero
  exact (hs.map (f.app U).hom).ne_zero (he.symm.trans hz)

def lineBundlePullbackGeneratorCoefficient [IsIntegral X] (U : Y.Opens) [Nonempty (f ⁻¹ᵁ U)]
    (s : Γ(L.sheaf, U)) (hs : IsUnit (GlobalFrame.Cycles.lineBundleGlobalFrame e U s)) : X.functionFieldˣ :=
  Units.mk0 ((L.pullback f).genericSectionCoefficient (f ⁻¹ᵁ U) (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf U s))
    ((L.pullback f).genericSectionCoefficient_ne_zero (f ⁻¹ᵁ U) _
      (lineBundlePullbackSection_ne_zero f L e U s hs))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.PullbackGenerator.Cycles
