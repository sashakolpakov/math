import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IdealModuleGenerator
import OAI.AlgebraicGeometry.Divisors.LineBundles.Module.SectionHom

/-! # Ideal Open Generator -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IdealOpenGenerator.BundleCycles

noncomputable section

/-! A section generating the actual regular principal kernels on
subopens gives a frame for the restricted ideal module. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Z : Scheme.{0}} (f : Z ⟶ X) (U : X.Opens) (s : Γ(SchemeIdealModule.BundleCycles.schemeIdealModule f, U))

theorem schemeIdealOpenSectionHom_bijective (V : U.toScheme.Opens)
    (hreg : IsRegular (X.presheaf.map (homOfLE (Module.SectionHom.BundleCycles.openInclusionImage_le U V)).op
      ((SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion f).app U s)))
    (hker : RingHom.ker (f.app (U.ι ''ᵁ V)).hom =
      Ideal.span {X.presheaf.map (homOfLE (Module.SectionHom.BundleCycles.openInclusionImage_le U V)).op
        ((SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion f).app U s)}) :
    Function.Bijective ((Module.SectionHom.BundleCycles.moduleSectionHomOnOpen (SchemeIdealModule.BundleCycles.schemeIdealModule f) U s).app V) := by
  let q := (SchemeIdealModule.BundleCycles.schemeIdealModule f).presheaf.map (homOfLE (Module.SectionHom.BundleCycles.openInclusionImage_le U V)).op s
  have hq : IdealModule.BundleCycles.schemeIdealModuleSectionLinear f (U.ι ''ᵁ V) q =
      X.presheaf.map (homOfLE (Module.SectionHom.BundleCycles.openInclusionImage_le U V)).op ((SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion f).app U s) :=
    (IdealModule.BundleCycles.schemeIdealModuleSectionLinear_apply f _ q).trans (IdealModule.BundleCycles.schemeIdealModuleInclusion_restrict f _ s)
  have hr : IsRegular (IdealModule.BundleCycles.schemeIdealModuleSectionLinear f (U.ι ''ᵁ V) q) := hq.symm ▸ hreg
  have hspan : ∀ m, IdealModule.BundleCycles.schemeIdealModuleSectionLinear f (U.ι ''ᵁ V) m ∈
      Ideal.span {IdealModule.BundleCycles.schemeIdealModuleSectionLinear f (U.ι ''ᵁ V) q} := by
    intro m
    rw [hq, ← hker]
    exact IdealModule.BundleCycles.schemeIdealModuleSectionLinear_mem f _ m
  have hb := RegularPrincipalGenerator.BundleCycles.regularPrincipalGenerator_bijective (IdealModule.BundleCycles.schemeIdealModuleSectionLinear f (U.ι ''ᵁ V))
    (IdealModule.BundleCycles.schemeIdealModuleSectionLinear_injective f _) q hr hspan
  have he : (fun r : Γ(U.toScheme, V) => (Module.SectionHom.BundleCycles.moduleSectionHomOnOpen (SchemeIdealModule.BundleCycles.schemeIdealModule f) U s).app V r) =
      (fun r : Γ(X, U.ι ''ᵁ V) => r • q) := by
    funext r
    have h := Module.SectionHom.BundleCycles.moduleSectionHomOnOpen_app (SchemeIdealModule.BundleCycles.schemeIdealModule f) U s V r
    rw [Module.SectionHom.BundleCycles.moduleSectionAsGlobal_restrict] at h
    exact h.trans (LineBundle.Frames.Cycles.LineBundleConstruction.openRestriction_smul (SchemeIdealModule.BundleCycles.schemeIdealModule f) U V r q).symm
  exact (congrArg Function.Bijective he).mpr hb

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IdealOpenGenerator.BundleCycles
