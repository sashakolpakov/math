import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TrivialBundleSectionSurjectivity

/-! # Trivial Bundle Section Bijectivity -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TrivialBundleSectionBijectivity.Construction

noncomputable section

/-! Pullback of sections of a trivial bundle is bijective when the map on global functions is. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem structureSheaf_sections_bijective_of_appTop
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIso f.appTop] :
    Function.Bijective (PullbackModuleSections.Construction.modulePullbackGlobalSection f (LineBundle.Construction.structureSheafModule X)) := by
  have hf := ConcreteCategory.bijective_of_isIso f.appTop
  constructor
  · intro x y hxy
    apply hf.injective
    exact (PullbackModuleSections.Construction.modulePullbackGlobalSection_unit f x).symm.trans
      ((congrArg ((LineBundle.Construction.pullbackStructureSheafIso f).hom.app ⊤) hxy).trans
        (PullbackModuleSections.Construction.modulePullbackGlobalSection_unit f y))
  · exact TrivialBundleSectionSurjectivity.Construction.structureSheaf_sections_surjective_of_appTop f hf.surjective

theorem modulePullback_sections_bijective_of_iso
    {X Y : Scheme.{u}} (f : Y ⟶ X) {M N : X.Modules} (e : M ≅ N)
    (hN : Function.Bijective (PullbackModuleSections.Construction.modulePullbackGlobalSection f N)) :
    Function.Bijective (PullbackModuleSections.Construction.modulePullbackGlobalSection f M) := by
  constructor
  · intro x y hxy
    apply (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).injective
    apply hN.injective
    exact (PullbackModuleSections.Construction.modulePullbackGlobalSection_naturality f e.hom x).symm.trans
      ((congrArg (((Scheme.Modules.pullback f).map e.hom).app ⊤) hxy).trans
        (PullbackModuleSections.Construction.modulePullbackGlobalSection_naturality f e.hom y))
  · exact TrivialBundleSectionSurjectivity.Construction.modulePullback_sections_surjective_of_iso f e hN.surjective

theorem trivialBundle_sections_bijective_of_appTop
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIso f.appTop]
    (M : X.Modules) (e : M ≅ LineBundle.Construction.structureSheafModule X) :
    Function.Bijective (PullbackModuleSections.Construction.modulePullbackGlobalSection f M) :=
  modulePullback_sections_bijective_of_iso f e (structureSheaf_sections_bijective_of_appTop f)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TrivialBundleSectionBijectivity.Construction
