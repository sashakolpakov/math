import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IdealOpenGenerator
import Mathlib.Topology.Sheaves.Stalks

/-! # Ideal Away -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IdealAway.BundleCycles

noncomputable section

/-! The actual ideal module restricts to the structure sheaf on any
open disjoint from the image of the scheme morphism. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Z : Scheme.{0}} (f : Z ⟶ X) (U : X.Opens)
    (hU : ∀ z : Z, f z ∉ U)

include hU in
theorem schemeIdeal_kernel_away : RingHom.ker (f.app U).hom = ⊤ := by
  apply top_unique
  intro r _
  change (f.app U) r = 0
  have he : f ⁻¹ᵁ U = ⊥ := by
    ext z
    exact iff_false_intro (hU z)
  let : Subsingleton Γ(Z, f ⁻¹ᵁ U) := by rw [he]; infer_instance
  exact Subsingleton.elim _ _

def schemeIdealAwaySection : Γ(SchemeIdealModule.BundleCycles.schemeIdealModule f, U) :=
  (IdealModule.BundleCycles.schemeIdealModuleSectionsIso f U).inv ⟨1, by rw [schemeIdeal_kernel_away f U hU]; trivial⟩

theorem schemeIdealAwaySection_image :
    (SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion f).app U (schemeIdealAwaySection f U hU) = (1 : Γ(X, U)) :=
  IdealModule.BundleCycles.schemeIdealModuleSectionsIso_inv_apply f U _

include hU in
theorem schemeIdealAwaySectionHom_isIso :
    IsIso (Module.SectionHom.BundleCycles.moduleSectionHomOnOpen (SchemeIdealModule.BundleCycles.schemeIdealModule f) U (schemeIdealAwaySection f U hU)) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro V
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  apply IdealOpenGenerator.BundleCycles.schemeIdealOpenSectionHom_bijective
  · rw [schemeIdealAwaySection_image, map_one]
    exact isRegular_one
  · rw [schemeIdealAwaySection_image, map_one, Ideal.span_singleton_one]
    exact schemeIdeal_kernel_away f (U.ι ''ᵁ V) (fun z hz => hU z (Module.SectionHom.BundleCycles.openInclusionImage_le U V hz))

def schemeIdealAwayTrivialization :
    (SchemeIdealModule.BundleCycles.schemeIdealModule f).restrict U.ι ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule U.toScheme := by
  let := schemeIdealAwaySectionHom_isIso f U hU
  exact (asIso (Module.SectionHom.BundleCycles.moduleSectionHomOnOpen (SchemeIdealModule.BundleCycles.schemeIdealModule f) U (schemeIdealAwaySection f U hU))).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IdealAway.BundleCycles
