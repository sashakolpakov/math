import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.PullbackGeneratorOpen
import OAI.AlgebraicGeometry.Divisors.LineBundles.Module.PullbackOpenIso
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RationalCoefficient
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenRestriction

/-! # Local Generator Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.LocalGeneratorPullback.Cycles

noncomputable section

/-! # LineBundleCycles: actual local line-bundle generators survive arbitrary pullback and define nonzero generic coefficients -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y)
    (U : Y.Opens) (e : L.sheaf.restrict U.ι ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule U.toScheme)
    (s : Γ(L.sheaf, U))
    (hs : IsUnit (GlobalFrame.Cycles.lineBundleGlobalFrame (L := L.restrictToOpen U.ι) e ⊤ (Module.SectionHom.BundleCycles.moduleSectionAsGlobal L.sheaf U s)))

include e hs in
theorem lineBundlePullback_localGenerator_ne_zero [Nonempty (f ⁻¹ᵁ U)] :
    Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf U s ≠ 0 := by
  let V := f ⁻¹ᵁ U
  let q := f ∣_ U
  let : Nonempty (⊤ : V.toScheme.Opens) := ⟨⟨Classical.choice (inferInstance : Nonempty V), trivial⟩⟩
  have hn : Module.OpenPullbackSections.BundleCycles.moduleGlobalSectionPullback q (L.sheaf.restrict U.ι) (Module.SectionHom.BundleCycles.moduleSectionAsGlobal L.sheaf U s) ≠ 0 :=
    PullbackGeneratorOpen.Cycles.lineBundlePullbackSectionToOpen_ne_zero q (L := L.restrictToOpen U.ι) e ⊤ ⊤
      (fun _ _ => trivial) (Module.SectionHom.BundleCycles.moduleSectionAsGlobal L.sheaf U s) hs
  intro hz
  have hz' : Module.SectionHom.BundleCycles.moduleSectionAsGlobal ((Scheme.Modules.pullback f).obj L.sheaf) V
      (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf U s) = 0 :=
    (congrArg (fun z => Module.SectionHom.BundleCycles.moduleSectionAsGlobal ((Scheme.Modules.pullback f).obj L.sheaf) V z) hz).trans
      (((Scheme.Modules.pullback f).obj L.sheaf).presheaf.map
        (homOfLE (Module.SectionHom.BundleCycles.openInclusionImage_le V ⊤)).op).hom.map_zero
  have he := Module.PullbackOpenIso.BundleCycles.modulePullbackOpenIso_section f L.sheaf U s
  have hzero := (congrArg (fun z => (Module.PullbackOpenIso.BundleCycles.modulePullbackOpenIso f L.sheaf U).hom.app ⊤ z) hz').trans
    ((Module.PullbackOpenIso.BundleCycles.modulePullbackOpenIso f L.sheaf U).hom.app ⊤).hom.map_zero
  exact hn (he.symm.trans hzero)

def lineBundleLocalGeneratorPullbackCoefficient [IsIntegral X] [Nonempty (f ⁻¹ᵁ U)] : X.functionFieldˣ :=
  Units.mk0 ((L.pullback f).genericSectionCoefficient (f ⁻¹ᵁ U) (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf U s))
    ((L.pullback f).genericSectionCoefficient_ne_zero (f ⁻¹ᵁ U) _
      (lineBundlePullback_localGenerator_ne_zero f L U e s hs))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.LocalGeneratorPullback.Cycles
