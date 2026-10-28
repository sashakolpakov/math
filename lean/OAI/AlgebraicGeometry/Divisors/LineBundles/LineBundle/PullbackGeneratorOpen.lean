import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.PullbackGenerator
import OAI.AlgebraicGeometry.Divisors.LineBundles.Module.SectionPullbackComposition

/-! # Pullback Generator Open -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.PullbackGeneratorOpen.Cycles

noncomputable section

/-! # LineBundleCycles: generator coordinates and nonvanishing after pullback to a smaller nonempty open -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} (f : X ⟶ Y) {L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y}
    (e : L.sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule Y)

theorem lineBundlePullbackGlobalTrivialization_section_toOpen
    (U : Y.Opens) (V : X.Opens) (hV : V ≤ f ⁻¹ᵁ U) (s : Γ(L.sheaf, U)) :
    (PullbackIso.Cycles.lineBundlePullbackGlobalTrivialization e f).hom.app V (Module.SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen f L.sheaf U V hV s) =
      f.appLE U V hV (GlobalFrame.Cycles.lineBundleGlobalFrame e U s) := by
  have H := ConcreteCategory.congr_hom
    ((PullbackIso.Cycles.lineBundlePullbackGlobalTrivialization e f).hom.mapPresheaf.naturality (homOfLE hV).op)
    (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf U s)
  exact H.trans (congrArg (fun r : Γ(X, f ⁻¹ᵁ U) => X.presheaf.map (homOfLE hV).op r)
    (Module.PullbackUnitSections.BundleCycles.lineBundlePullbackGlobalTrivialization_section f e U s))

theorem lineBundlePullbackSectionToOpen_ne_zero (U : Y.Opens) (V : X.Opens) [Nonempty V]
    (hV : V ≤ f ⁻¹ᵁ U) (s : Γ(L.sheaf, U)) (hs : IsUnit (GlobalFrame.Cycles.lineBundleGlobalFrame e U s)) :
    Module.SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen f L.sheaf U V hV s ≠ 0 := by
  intro hz
  have H := lineBundlePullbackGlobalTrivialization_section_toOpen f e U V hV s
  have hzero := (congrArg (fun z => (PullbackIso.Cycles.lineBundlePullbackGlobalTrivialization e f).hom.app V z) hz).trans
    ((PullbackIso.Cycles.lineBundlePullbackGlobalTrivialization e f).hom.app V).hom.map_zero
  exact (hs.map (f.appLE U V hV).hom).ne_zero (H.symm.trans hzero)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.PullbackGeneratorOpen.Cycles
