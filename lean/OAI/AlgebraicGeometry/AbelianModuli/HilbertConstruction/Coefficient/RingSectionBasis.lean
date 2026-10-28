import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ModuleSectionIdentity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionValueAdditive
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.SectionNonvanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.NonvanishingAddition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisSectionRatioSubring

/-! # Ring Section Basis -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.RingSectionBasis

noncomputable section

/-! Section bases over any coefficient ring give actual sheaf sections,
finite scalar decompositions, and generation of their regular ratios. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators
universe u v
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

def coefficientRingSectionAddEquiv (c : R →+* Γ(X, ⊤)) (M : X.Modules) :
    (Line.Bundles.structureModule X ⟶ M) ≃+ (GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).obj M where
  __ := (Global.Sections.moduleSectionHomEquiv M).trans (Global.ModuleSectionIdentity.coefficientGlobalSectionsNativeIso c M).symm.toEquiv
  map_add' _ _ := rfl

theorem coefficientRingSectionAddEquiv_scalar (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    (r : R) (s : Line.Bundles.structureModule X ⟶ M) :
    coefficientRingSectionAddEquiv c M (Scalar.SectionValues.scalarSection (c r) s) =
      r • coefficientRingSectionAddEquiv c M s := by
  apply (Global.ModuleSectionIdentity.coefficientGlobalSectionsNativeIso c M).injective
  rw [map_smul]
  change (Global.ModuleSectionIdentity.coefficientGlobalSectionsNativeIso c M)
    ((Global.ModuleSectionIdentity.coefficientGlobalSectionsNativeIso c M).symm (Global.Sections.moduleSectionHomEquiv M (Scalar.SectionValues.scalarSection (c r) s))) =
      r • (Global.ModuleSectionIdentity.coefficientGlobalSectionsNativeIso c M)
        ((Global.ModuleSectionIdentity.coefficientGlobalSectionsNativeIso c M).symm (Global.Sections.moduleSectionHomEquiv M s))
  erw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact Scalar.SectionValues.scalarSection_globalValue (c r) s

def coefficientRingBasisFamily (c : R →+* Γ(X, ⊤)) (M : X.Modules) {ι : Type v}
    (b : Module.Basis ι R ((GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).obj M)) :
    ι → (Line.Bundles.structureModule X ⟶ M) := fun i => (coefficientRingSectionAddEquiv c M).symm (b i)

theorem section_eq_coefficientRing_basis_sum (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type v} [Fintype ι] (b : Module.Basis ι R ((GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).obj M))
    (s : Line.Bundles.structureModule X ⟶ M) :
    s = ∑ i, Scalar.SectionValues.scalarSection (c (b.repr (coefficientRingSectionAddEquiv c M s) i))
      (coefficientRingBasisFamily c M b i) := by
  apply (coefficientRingSectionAddEquiv c M).injective
  rw [map_sum]
  simp only [coefficientRingSectionAddEquiv_scalar, coefficientRingBasisFamily,
    AddEquiv.apply_symm_apply]
  exact (b.sum_repr (coefficientRingSectionAddEquiv c M s)).symm

theorem coefficientRingBasisFamily_covers (c : R →+* Γ(X, ⊤)) (L : Line.Bundles.LineBundle X)
    {ι : Type v} [Fintype ι] (b : Module.Basis ι R ((GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).obj L.sheaf))
    (h : ∀ x : X, ∃ s : Line.Bundles.structureModule X ⟶ L.sheaf, x ∈ Ample.LineBundles.sectionNonvanishing s) :
    ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (coefficientRingBasisFamily c L.sheaf b i) := by
  intro x
  obtain ⟨s, hs⟩ := h x
  rw [section_eq_coefficientRing_basis_sum c L.sheaf b s] at hs
  obtain ⟨i, _, hi⟩ := L.mem_sectionNonvanishing_sum Finset.univ _ x hs
  exact ⟨i, Scalar.SectionNonvanishing.scalarSection_nonvanishing_le L _ _ hi⟩

theorem pullbackSection_scalarSection {Y : Scheme.{u}} (f : Y ⟶ X) {M : X.Modules}
    (r : Γ(X, ⊤)) (s : Line.Bundles.structureModule X ⟶ M) :
    Ample.LineBundles.pullbackSection f (Scalar.SectionValues.scalarSection r s) = Scalar.SectionValues.scalarSection (f.appTop r) (Ample.LineBundles.pullbackSection f s) := by
  apply (Global.Sections.moduleSectionHomEquiv _).injective
  rw [Pullback.SectionGlobalValue.pullbackSection_globalValue, Scalar.SectionValues.scalarSection_globalValue, Scalar.SectionValues.scalarSection_globalValue,
    Pullback.SectionGlobalValue.pullbackSection_globalValue]
  exact ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app_smul
    r (Global.Sections.moduleSectionHomEquiv M s)

theorem sectionRatio_scalarSection {M : X.Modules}
    (s t : Line.Bundles.structureModule X ⟶ M) (r : Γ(X, ⊤)) :
    Section.Frames.sectionRatio s (Scalar.SectionValues.scalarSection r t) =
      (Ample.LineBundles.sectionNonvanishing s).ι.appTop r * Section.Frames.sectionRatio s t := by
  rw [Frame.Coordinates.sectionRatio_eq_frameCoordinate, Frame.Coordinates.sectionRatio_eq_frameCoordinate, pullbackSection_scalarSection]
  let U := Ample.LineBundles.sectionNonvanishing s
  change Frame.Coordinates.structureModuleEndValue U.toScheme
    ((Scalar.SectionValues.scalarSection (U.ι.appTop r) (Ample.LineBundles.pullbackSection U.ι t)) ≫ inv (Ample.LineBundles.pullbackSection U.ι s)) = _
  rw [show Scalar.SectionValues.scalarSection (U.ι.appTop r) (Ample.LineBundles.pullbackSection U.ι t) ≫ inv (Ample.LineBundles.pullbackSection U.ι s) =
      Scalar.SectionValues.scalarSection (U.ι.appTop r) (Ample.LineBundles.pullbackSection U.ι t ≫ inv (Ample.LineBundles.pullbackSection U.ι s)) from
        Category.assoc _ _ _]
  exact Scalar.SectionValues.scalarSection_globalValue (U.ι.appTop r)
    (Ample.LineBundles.pullbackSection U.ι t ≫ inv (Ample.LineBundles.pullbackSection U.ι s))

theorem sectionRatio_mem_of_coefficientRing_basis (c : R →+* Γ(X, ⊤)) {M : X.Modules}
    (s : Line.Bundles.structureModule X ⟶ M) {ι : Type v} [Fintype ι]
    (b : Module.Basis ι R ((GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).obj M))
    (C : Subring Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤))
    (hc : ∀ r : R, (Ample.LineBundles.sectionNonvanishing s).ι.appTop (c r) ∈ C)
    (hb : ∀ i, Section.Frames.sectionRatio s (coefficientRingBasisFamily c M b i) ∈ C)
    (t : Line.Bundles.structureModule X ⟶ M) : Section.Frames.sectionRatio s t ∈ C := by
  rw [section_eq_coefficientRing_basis_sum c M b t]
  change BasisSectionRatioSubring.sectionRatioAddHom s (∑ i,
    Scalar.SectionValues.scalarSection (c (b.repr (coefficientRingSectionAddEquiv c M t) i))
      (coefficientRingBasisFamily c M b i)) ∈ C
  rw [map_sum]
  apply C.sum_mem
  intro i _
  change Section.Frames.sectionRatio s (Scalar.SectionValues.scalarSection _ (coefficientRingBasisFamily c M b i)) ∈ C
  rw [sectionRatio_scalarSection]
  exact C.mul_mem (hc _) (hb i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.RingSectionBasis
