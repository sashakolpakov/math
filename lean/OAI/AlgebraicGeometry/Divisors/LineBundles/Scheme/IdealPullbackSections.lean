import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IdealPullbackMap
import OAI.AlgebraicGeometry.Divisors.LineBundles.Module.PullbackUnitSections
import OAI.AlgebraicGeometry.Divisors.LineBundles.Module.SectionPullbackComposition

/-! # Ideal Pullback Sections -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IdealPullbackSections.BundleCycles

noncomputable section

/-! The canonical ideal pullback map sends actual local ideal
sections to the ordinary pullback of their regular functions. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Z X' Z' : Scheme.{0}} (i : Z ⟶ X) (j : Z' ⟶ X')
    (f : X' ⟶ X) (g : Z' ⟶ Z) (h : g ≫ i = j ≫ f)

theorem schemeIdealPullbackMap_section_image (U : X.Opens) (s : Γ(SchemeIdealModule.BundleCycles.schemeIdealModule i, U)) :
    (SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion j).app (f ⁻¹ᵁ U)
      ((IdealPullbackMap.BundleCycles.schemeIdealPullbackMap i j f g h).app (f ⁻¹ᵁ U)
        (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f (SchemeIdealModule.BundleCycles.schemeIdealModule i) U s)) =
      f.app U ((SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i).app U s) := by
  have H := ConcreteCategory.congr_hom
    (congrArg (fun k => k.app (f ⁻¹ᵁ U)) (IdealPullbackMap.BundleCycles.schemeIdealPullbackMap_inclusion i j f g h))
      (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f (SchemeIdealModule.BundleCycles.schemeIdealModule i) U s)
  have H₁ := Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen_naturality f (SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i) U s
  have H₂ := Module.PullbackUnitSections.BundleCycles.modulePullbackUnitIso_section f U ((SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i).app U s)
  exact H.trans ((congrArg ((LineBundle.OpenRestriction.Cycles.modulePullbackUnitIso f).hom.app (f ⁻¹ᵁ U)) H₁).trans H₂)

theorem schemeIdealPullbackMap_sectionToOpen_image (U : X.Opens) (V : X'.Opens)
    (hV : V ≤ f ⁻¹ᵁ U) (s : Γ(SchemeIdealModule.BundleCycles.schemeIdealModule i, U)) :
    (SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion j).app V
      ((IdealPullbackMap.BundleCycles.schemeIdealPullbackMap i j f g h).app V
        (Module.SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen f (SchemeIdealModule.BundleCycles.schemeIdealModule i) U V hV s)) =
      f.appLE U V hV ((SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i).app U s) := by
  let φ := IdealPullbackMap.BundleCycles.schemeIdealPullbackMap i j f g h ≫ SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion j
  have H := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE hV).op)
    (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f (SchemeIdealModule.BundleCycles.schemeIdealModule i) U s)
  have H' := congrArg (X'.presheaf.map (homOfLE hV).op)
    (schemeIdealPullbackMap_section_image i j f g h U s)
  exact H.trans H'

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IdealPullbackSections.BundleCycles
