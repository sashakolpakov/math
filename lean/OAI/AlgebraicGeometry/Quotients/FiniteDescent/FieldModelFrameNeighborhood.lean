import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModelFrame
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Field Model Frame Neighborhood -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.FieldModelFrameNeighborhood

noncomputable section

/-! A cycle detected after an arbitrary field-valued base change gives a
frame near that field point. The Cartesian square retains the full base. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules
universe u

namespace Construction.SectionTrivialityOpen

theorem mem_of_cartesian_frame
    {X S Y T : Scheme.{u}} (π : X ⟶ S) [IsProper π]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf)
    (f : Y ⟶ X) (ρ : Y ⟶ T) (q : T ⟶ S) (H : IsPullback f ρ π q)
    (t : T) (hs : IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s)) : q t ∈ SectionTriviality.Construction.SectionTrivialityOpen.baseOpen π L s := by
  have : IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) := hs
  have hn : f ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s = ⊤ :=
    (SectionBase.Construction.SectionBaseChange.nonvanishing_pullback f L s).symm.trans
      ((AbelianModuli.HilbertConstruction.Section.Frames.isIso_iff_sectionNonvanishing_eq_top (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s)).mp hs)
  change q t ∉ π '' (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s : Set X)ᶜ
  rintro ⟨x, hx, hxq⟩
  have hr : x ∈ Set.range (pullback.fst π q) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨t, hxq.symm⟩
  obtain ⟨z, hz⟩ := hr
  let y := H.isoPullback.inv z
  have hy : f y = x :=
    (congrArg (fun k : pullback π q ⟶ X => k z) H.isoPullback_inv_fst).trans hz
  have hmem : f y ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s := by
    change y ∈ f ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s
    rw [hn]
    trivial
  exact hx (hy ▸ hmem)

theorem isIso_of_baseOpen_eq_top
    {X S : Scheme.{u}} (π : X ⟶ S) [IsProper π]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf)
    (h : SectionTriviality.Construction.SectionTrivialityOpen.baseOpen π L s = ⊤) : IsIso s := by
  apply (AbelianModuli.HilbertConstruction.Section.Frames.isIso_iff_sectionNonvanishing_eq_top s).mpr
  apply top_unique
  intro x _
  have hx : π x ∈ SectionTriviality.Construction.SectionTrivialityOpen.baseOpen π L s := by rw [h]; trivial
  by_contra hn
  exact hx ⟨x, hn, rfl⟩

end Construction.SectionTrivialityOpen

namespace Construction.ModelFrameNeighborhood

theorem exists_open_of_field_point
    {X S Y : Scheme.{u}} (π : X ⟶ S) [IsProper π] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
    {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π L.sheaf U) [QuasiIsoAt φ 0]
    {K : Type u} [Field K] (q : Spec (.of K) ⟶ S)
    (f : Y ⟶ X) (ρ : Y ⟶ Spec (.of K)) (H : IsPullback f ρ π q)
    [ConnectedSpace Y] [IsReduced Y]
    (he : Nonempty ((L.pullback f).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y))
    (hφ : QuasiIsoAt (CechModelBaseChange.Construction.CechBaseChangeMap.modelMap f π ρ q H.w L.sheaf U φ) 0)
    (z : (D.d 0 1).hom.ker) (hz : (ModelOneTensor.Construction.CechBaseChangeMap.oneCycle q z).val ≠ 0) :
    ∃ V : S.Opens, q (IsLocalRing.closedPoint K) ∈ V ∧
      Nonempty ((L.pullback (π ⁻¹ᵁ V).ι).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π ⁻¹ᵁ V).toScheme) := by
  have := hφ
  let a := GlobalModel.Construction.GlobalModelSections.equiv π L.sheaf U hU φ z
  let s := (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).symm a
  have hs : AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s ≠ 0 := by
    intro h
    have ha := PullbackSectionValue.Construction.PullbackSectionZero.value_zero f s h
    have hv : AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf s = a :=
      (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).apply_symm_apply a
    rw [hv] at ha
    exact ModelFiberNonzero.Construction.CechBaseChangeMap.global_section_pullback_ne_zero f π ρ q H.w
      L.sheaf U hU φ z hz ha
  let F : Over (Spec (.of K)) := Over.mk ρ
  have : IsProper F.hom := MorphismProperty.of_isPullback (P := @IsProper) H inferInstance
  have : ConnectedSpace F.left := inferInstanceAs (ConnectedSpace Y)
  have : IsReduced F.left := inferInstanceAs (IsReduced Y)
  have hi := TrivialBundle.Construction.TrivialBundleFrame.isIso F he.some (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) hs
  refine ⟨SectionTriviality.Construction.SectionTrivialityOpen.baseOpen π L s,
    SectionTrivialityOpen.mem_of_cartesian_frame π L s f ρ q H (IsLocalRing.closedPoint K) hi, ?_⟩
  have := SectionTriviality.Construction.SectionTrivialityOpen.isIso_restrict π L s
  exact ⟨(asIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (π ⁻¹ᵁ SectionTriviality.Construction.SectionTrivialityOpen.baseOpen π L s).ι s)).symm⟩

end Construction.ModelFrameNeighborhood

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.FieldModelFrameNeighborhood
