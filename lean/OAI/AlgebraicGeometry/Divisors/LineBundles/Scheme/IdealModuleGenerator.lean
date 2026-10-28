import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IdealModule
import OAI.AlgebraicGeometry.Divisors.LineBundles.RegularPrincipalGenerator
import OAI.AlgebraicGeometry.Divisors.LineBundles.Module.SectionHom
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Ideal Module Generator -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IdealModuleGenerator.BundleCycles

noncomputable section

/-! A section whose image regularly generates the actual function-ring
kernels trivializes the genuine ideal module. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Z : Scheme.{0}} (f : Z ⟶ X) (s : Γ(SchemeIdealModule.BundleCycles.schemeIdealModule f, ⊤))

theorem schemeIdealSectionHom_bijective (U : X.Opens)
    (hreg : IsRegular (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ((SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion f).app ⊤ s)))
    (hker : RingHom.ker (f.app U).hom =
      Ideal.span {X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ((SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion f).app ⊤ s)}) :
    Function.Bijective ((Module.SectionHom.BundleCycles.moduleSectionHom (SchemeIdealModule.BundleCycles.schemeIdealModule f) s).app U) := by
  let q := (SchemeIdealModule.BundleCycles.schemeIdealModule f).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s
  have hq : IdealModule.BundleCycles.schemeIdealModuleSectionLinear f U q =
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ((SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion f).app ⊤ s) :=
    (IdealModule.BundleCycles.schemeIdealModuleSectionLinear_apply f U q).trans (IdealModule.BundleCycles.schemeIdealModuleInclusion_restrict f le_top s)
  have hr : IsRegular (IdealModule.BundleCycles.schemeIdealModuleSectionLinear f U q) := hq.symm ▸ hreg
  have hspan : ∀ m, IdealModule.BundleCycles.schemeIdealModuleSectionLinear f U m ∈ Ideal.span {IdealModule.BundleCycles.schemeIdealModuleSectionLinear f U q} := by
    intro m
    rw [hq, ← hker]
    exact IdealModule.BundleCycles.schemeIdealModuleSectionLinear_mem f U m
  exact RegularPrincipalGenerator.BundleCycles.regularPrincipalGenerator_bijective (IdealModule.BundleCycles.schemeIdealModuleSectionLinear f U)
    (IdealModule.BundleCycles.schemeIdealModuleSectionLinear_injective f U) q hr hspan

theorem schemeIdealSectionHom_isIso
    (hreg : ∀ U : X.Opens, IsRegular
      (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ((SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion f).app ⊤ s)))
    (hker : ∀ U : X.Opens, RingHom.ker (f.app U).hom =
      Ideal.span {X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ((SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion f).app ⊤ s)}) :
    IsIso (Module.SectionHom.BundleCycles.moduleSectionHom (SchemeIdealModule.BundleCycles.schemeIdealModule f) s) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  exact (ConcreteCategory.isIso_iff_bijective _).mpr (schemeIdealSectionHom_bijective f s U (hreg U) (hker U))

def schemeIdealModuleTrivialization
    (hreg : ∀ U : X.Opens, IsRegular
      (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ((SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion f).app ⊤ s)))
    (hker : ∀ U : X.Opens, RingHom.ker (f.app U).hom =
      Ideal.span {X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ((SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion f).app ⊤ s)}) :
    SchemeIdealModule.BundleCycles.schemeIdealModule f ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule X := by
  let := schemeIdealSectionHom_isIso f s hreg hker
  exact (asIso (Module.SectionHom.BundleCycles.moduleSectionHom (SchemeIdealModule.BundleCycles.schemeIdealModule f) s)).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IdealModuleGenerator.BundleCycles
