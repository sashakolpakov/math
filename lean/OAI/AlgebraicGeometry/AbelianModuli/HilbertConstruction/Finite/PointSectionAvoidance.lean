import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.LineBundleSectionCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ScalarSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.NonvanishingAddition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ModuleSectionIdentity
import Mathlib.Algebra.Module.Submodule.Union

/-! # Point Section Avoidance -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.PointSectionAvoidance

noncomputable section

/-! Over an infinite field, a globally generated line bundle has an actual section nonvanishing at any prescribed finite family of scheme points, including nonclosed generic points. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v
variable {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X)

private def coefficientSectionValueEquiv :
    (Line.Bundles.structureModule X ⟶ L.sheaf) ≃+ (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj L.sheaf where
  __ := (Global.Sections.moduleSectionHomEquiv L.sheaf).trans
    (Global.ModuleSectionIdentity.coefficientGlobalSectionsNativeIso (Coefficient.ModulePresheaf.schemeCoefficientMap p) L.sheaf).symm.toEquiv
  map_add' s t := by
    change Global.Sections.moduleSectionHomEquiv L.sheaf (s + t) =
      Global.Sections.moduleSectionHomEquiv L.sheaf s + Global.Sections.moduleSectionHomEquiv L.sheaf t
    rfl

private theorem coefficientSectionValueEquiv_scalar (c : K) (s : Line.Bundles.structureModule X ⟶ L.sheaf) :
    coefficientSectionValueEquiv p L (Coefficient.ScalarSections.coefficientScalarSection p c s) =
      c • coefficientSectionValueEquiv p L s := by
  change (show (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj L.sheaf from
    Global.Sections.moduleSectionHomEquiv L.sheaf (Coefficient.ScalarSections.coefficientScalarSection p c s)) =
      c • (show (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj L.sheaf from Global.Sections.moduleSectionHomEquiv L.sheaf s)
  exact Coefficient.ScalarSections.coefficientScalarSection_value p c s

def sectionVanishingSubmodule (x : X) :
    Submodule K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj L.sheaf) where
  carrier := {v | x ∉ Ample.LineBundles.sectionNonvanishing ((coefficientSectionValueEquiv p L).symm v)}
  zero_mem' := by
    change x ∉ Ample.LineBundles.sectionNonvanishing ((coefficientSectionValueEquiv p L).symm 0)
    rw [map_zero, L.sectionNonvanishing_zero]
    exact fun h => h
  add_mem' := by
    intro v w hv hw
    change x ∉ Ample.LineBundles.sectionNonvanishing ((coefficientSectionValueEquiv p L).symm (v + w))
    rw [map_add]
    intro hx
    exact (L.sectionNonvanishing_add_le _ _ hx).elim hv hw
  smul_mem' := by
    intro c v hv
    have he : (coefficientSectionValueEquiv p L).symm (c • v) =
        Coefficient.ScalarSections.coefficientScalarSection p c ((coefficientSectionValueEquiv p L).symm v) := by
      apply (coefficientSectionValueEquiv p L).injective
      rw [AddEquiv.apply_symm_apply, coefficientSectionValueEquiv_scalar, AddEquiv.apply_symm_apply]
    change x ∉ Ample.LineBundles.sectionNonvanishing ((coefficientSectionValueEquiv p L).symm (c • v))
    rw [he]
    exact fun hx => hv (Coefficient.ScalarSections.coefficientScalarSection_nonvanishing_le p L c _ hx)

theorem sectionVanishingSubmodule_ne_top (x : X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (hs : x ∈ Ample.LineBundles.sectionNonvanishing s) :
    sectionVanishingSubmodule p L x ≠ ⊤ := by
  intro htop
  have hv : coefficientSectionValueEquiv p L s ∈ sectionVanishingSubmodule p L x := by
    rw [htop]
    trivial
  change x ∉ Ample.LineBundles.sectionNonvanishing
    ((coefficientSectionValueEquiv p L).symm (coefficientSectionValueEquiv p L s)) at hv
  rw [AddEquiv.symm_apply_apply] at hv
  exact hv hs

include p in
theorem exists_section_nonvanishing_at_finite_points [Infinite K]
    {ι : Type v} [Finite ι] (x : ι → X)
    (h : ∀ i, ∃ s : Line.Bundles.structureModule X ⟶ L.sheaf, x i ∈ Ample.LineBundles.sectionNonvanishing s) :
    ∃ s : Line.Bundles.structureModule X ⟶ L.sheaf, ∀ i, x i ∈ Ample.LineBundles.sectionNonvanishing s := by
  have hp (i : ι) : sectionVanishingSubmodule p L (x i) ≠ ⊤ := by
    obtain ⟨s, hs⟩ := h i
    exact sectionVanishingSubmodule_ne_top p L (x i) s hs
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun i => sectionVanishingSubmodule p L (x i)) hp
  refine ⟨(coefficientSectionValueEquiv p L).symm v, fun i => ?_⟩
  exact Classical.not_not.mp (hv i)

include p in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators.exists_section_nonvanishing_at_finite_points [Infinite K]
    (hL : GlobalModuleGenerators.HasFiniteGlobalGenerators L.sheaf) {ι : Type v} [Finite ι] (x : ι → X) :
    ∃ s : Line.Bundles.structureModule X ⟶ L.sheaf, ∀ i, x i ∈ Ample.LineBundles.sectionNonvanishing s := by
  obtain ⟨J, _, s, hs⟩ := hL.lineBundle_section_cover L
  apply PointSectionAvoidance.exists_section_nonvanishing_at_finite_points p L x
  intro i
  obtain ⟨j, hj⟩ := hs (x i)
  exact ⟨s j, hj⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.PointSectionAvoidance
