import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ModuleSectionIdentity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionValueAdditive
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.LinearCombinationNonvanishing
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Basis Section Generation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisSectionGeneration

noncomputable section

/-! A basis of the genuine finite-dimensional section space generates
wherever all global sections generate. The proof uses actual coefficient scalars. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v
variable {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K))

def coefficientSectionAddEquiv (M : X.Modules) :
    (Line.Bundles.structureModule X ⟶ M) ≃+ (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M where
  __ := (Global.Sections.moduleSectionHomEquiv M).trans
    (Global.ModuleSectionIdentity.coefficientGlobalSectionsNativeIso (Coefficient.ModulePresheaf.schemeCoefficientMap p) M).symm.toEquiv
  map_add' s t := by
    change Global.Sections.moduleSectionHomEquiv M (s + t) = Global.Sections.moduleSectionHomEquiv M s + Global.Sections.moduleSectionHomEquiv M t
    rfl

theorem coefficientSectionAddEquiv_scalar (M : X.Modules) (c : K) (s : Line.Bundles.structureModule X ⟶ M) :
    coefficientSectionAddEquiv p M (Coefficient.ScalarSections.coefficientScalarSection p c s) =
      c • coefficientSectionAddEquiv p M s := by
  change (show (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M from
    Global.Sections.moduleSectionHomEquiv M (Coefficient.ScalarSections.coefficientScalarSection p c s)) =
      c • (show (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M from Global.Sections.moduleSectionHomEquiv M s)
  exact Coefficient.ScalarSections.coefficientScalarSection_value p c s

def sectionBasisFamily (M : X.Modules) {ι : Type v}
    (b : Module.Basis ι K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M)) :
    ι → (Line.Bundles.structureModule X ⟶ M) :=
  fun i => (coefficientSectionAddEquiv p M).symm (b i)

theorem section_eq_basis_linearCombination (M : X.Modules) {ι : Type v} [Fintype ι]
    (b : Module.Basis ι K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M)) (s : Line.Bundles.structureModule X ⟶ M) :
    s = ∑ i, Coefficient.ScalarSections.coefficientScalarSection p (b.repr (coefficientSectionAddEquiv p M s) i)
      (sectionBasisFamily p M b i) := by
  apply (coefficientSectionAddEquiv p M).injective
  rw [map_sum]
  simp only [coefficientSectionAddEquiv_scalar, sectionBasisFamily, AddEquiv.apply_symm_apply]
  exact (b.sum_repr (coefficientSectionAddEquiv p M s)).symm

theorem sectionBasisFamily_covers (L : Line.Bundles.LineBundle X) {ι : Type v} [Fintype ι]
    (b : Module.Basis ι K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj L.sheaf))
    (h : ∀ x : X, ∃ s : Line.Bundles.structureModule X ⟶ L.sheaf, x ∈ Ample.LineBundles.sectionNonvanishing s) :
    ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (sectionBasisFamily p L.sheaf b i) := by
  intro x
  obtain ⟨s, hs⟩ := h x
  rw [section_eq_basis_linearCombination p L.sheaf b s] at hs
  obtain ⟨i, _, hi⟩ := Section.LinearCombinationNonvanishing.coefficient_linearCombination_nonvanishing p L Finset.univ
    (fun i => b.repr (coefficientSectionAddEquiv p L.sheaf s) i)
    (sectionBasisFamily p L.sheaf b) x hs
  exact ⟨i, hi⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisSectionGeneration
