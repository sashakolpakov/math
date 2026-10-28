import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperFunctionsEq
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ReducedSectionsEq
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorSection
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PicardPullbackId

/-! # Section Pair -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionPair.Construction.SectionPairTriviality

noncomputable section

/-! Two nonzero sections of inverse line bundles on a proper integral
scheme force both line bundles to be trivial. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

variable {K : Type u} [Field K] (X : Over (Spec (.of K)))
variable [IsProper X.hom] [IsIntegral X.left]

omit [IsProper X.hom] in
theorem nonempty_nonvanishing (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left ⟶ L.sheaf) (hs : s ≠ 0) :
    (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s : Set X.left).Nonempty := by
  by_contra h
  exact hs (ReducedSectionsEq.Construction.ReducedSections.section_eq_zero_of_nonvanishing_eq_bot L s
    ((TopologicalSpace.Opens.not_nonempty_iff_eq_bot _).mp h))

theorem isIso_of_pair (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left)
    (e : (L.tensor M).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left ⟶ L.sheaf) (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left ⟶ M.sheaf)
    (hs : s ≠ 0) (ht : t ≠ 0) : IsIso s := by
  let a : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left) := BinaryTensorId.Construction.BinaryTensorMap.tensorSection s t ≫ e.hom
  have he : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing a = AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s ⊓ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t :=
    (AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso _ e).trans (TensorSection.Construction.TensorSectionLocus.nonvanishing s t)
  have ha : (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing a : Set X.left).Nonempty := by
    rw [he]
    exact nonempty_preirreducible_inter (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).isOpen
      (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t).isOpen (nonempty_nonvanishing X L s hs)
      (nonempty_nonvanishing X M t ht)
  have hu : IsUnit (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X.left a) := by
    apply (ProperFunctionsEq.Construction.ProperFunctions.section_eq_zero_or_isUnit X _).resolve_left
    intro hz
    obtain ⟨x, hx⟩ := ha
    rw [AbelianModuli.HilbertConstruction.Scalar.Nonvanishing.sectionNonvanishing_scalar, hz, X.left.basicOpen_zero] at hx
    exact hx.elim
  have : IsIso a := (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEnd_isIso_iff a).mpr hu
  have htop : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing a = ⊤ := (AbelianModuli.HilbertConstruction.Section.Frames.isIso_iff_sectionNonvanishing_eq_top a).mp this
  apply (AbelianModuli.HilbertConstruction.Section.Frames.isIso_iff_sectionNonvanishing_eq_top s).mpr
  apply top_unique
  exact htop.symm.trans_le (he.le.trans inf_le_left)

omit [IsProper X.hom] [IsIntegral X.left] in
theorem exists_nonzero_section (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) [Nontrivial Γ(L.sheaf, ⊤)] :
    ∃ s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left ⟶ L.sheaf, s ≠ 0 := by
  obtain ⟨z, hz⟩ := exists_ne (0 : Γ(L.sheaf, ⊤))
  refine ⟨(AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).symm z, ?_⟩
  intro h
  apply hz
  have he := congrArg (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf) h
  have hzero : AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf 0 = 0 := rfl
  exact (Equiv.apply_symm_apply _ _).symm.trans (he.trans hzero)

theorem trivial_of_sections (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left)
    (e : (L.tensor M).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left)
    [Nontrivial Γ(L.sheaf, ⊤)] [Nontrivial Γ(M.sheaf, ⊤)] :
    Nonempty (L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left) := by
  obtain ⟨s, hs⟩ := exists_nonzero_section X L
  obtain ⟨t, ht⟩ := exists_nonzero_section X M
  have := isIso_of_pair X L M e s t hs ht
  exact ⟨(asIso s).symm⟩

theorem nontrivial_sections_of_trivial (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left)
    (e : L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left) : Nontrivial Γ(L.sheaf, ⊤) := by
  have : Nontrivial Γ(X.left, ⊤) := (ProperFunctionsEq.Construction.ProperFunctions.globalSections_isField X).toField.toNontrivial
  let i := (SheafOfModules.evaluation X.left.ringCatSheaf (.op ⊤)).mapIso e
  exact i.toLinearEquiv.nontrivial_congr.mpr
    (show Nontrivial Γ(X.left, ⊤) from inferInstance)

theorem pair_iff (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left)
    (e : (L.tensor M).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left) :
    Nonempty (L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left) ↔
      Nontrivial Γ(L.sheaf, ⊤) ∧ Nontrivial Γ(M.sheaf, ⊤) := by
  constructor
  · rintro ⟨h⟩
    have hM : M.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left :=
      (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso M.sheaf).symm ≪≫
        AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr h.symm (Iso.refl M.sheaf) ≪≫ e
    exact ⟨nontrivial_sections_of_trivial X L h, nontrivial_sections_of_trivial X M hM⟩
  · rintro ⟨hL, hM⟩
    exact trivial_of_sections X L M e

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionPair.Construction.SectionPairTriviality
