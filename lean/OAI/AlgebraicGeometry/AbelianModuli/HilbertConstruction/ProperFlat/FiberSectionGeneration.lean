import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiberSectionSpanning
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.SectionNonvanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.LinearCombinationNonvanishing

/-! # Fiber Section Generation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiberSectionGeneration

noncomputable section

/-! Global generation on a fiber with vanishing first cohomology gives actual global sections nonvanishing at every point of that fiber. Compactness supplies a finite family. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem properFlat_global_sections_cover_fiber
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X) (x : S)
    (hH : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback (f.fiberι x)).sheaf 1))
    (hgen : ∀ y : f.fiber x, ∃ t : Line.Bundles.structureModule (f.fiber x) ⟶
      (L.pullback (f.fiberι x)).sheaf, y ∈ Ample.LineBundles.sectionNonvanishing t) :
    ∀ y : f.fiber x, ∃ s : Line.Bundles.structureModule X ⟶ L.sheaf,
      f.fiberι x y ∈ Ample.LineBundles.sectionNonvanishing s := by
  intro y
  obtain ⟨t, hyt⟩ := hgen y
  obtain ⟨k, c, s, ht⟩ := FiberSectionSpanning.properFlat_fiber_sections_spanned f L x hH t
  have hy : y ∈ Ample.LineBundles.sectionNonvanishing (∑ i,
      Scalar.SectionValues.scalarSection ((f.fiberToSpecResidueField x).appTop (c i))
        (Ample.LineBundles.pullbackSection (f.fiberι x) (s i))) :=
    (congrArg (fun z => y ∈ Ample.LineBundles.sectionNonvanishing z) ht).mp hyt
  obtain ⟨i, _, hi⟩ := (L.pullback (f.fiberι x)).mem_sectionNonvanishing_sum Finset.univ
    (fun i => Scalar.SectionValues.scalarSection ((f.fiberToSpecResidueField x).appTop (c i))
      (Ample.LineBundles.pullbackSection (f.fiberι x) (s i))) y hy
  have hiy := Scalar.SectionNonvanishing.scalarSection_nonvanishing_le (L.pullback (f.fiberι x))
    ((f.fiberToSpecResidueField x).appTop (c i)) (Ample.LineBundles.pullbackSection (f.fiberι x) (s i)) hi
  exact ⟨s i, (congrArg (fun U : (f.fiber x).Opens => y ∈ U)
    (LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange (f.fiberι x) L (s i))).mp hiy⟩

theorem properFlat_finite_global_sections_cover_fiber
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X) (x : S)
    (hH : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback (f.fiberι x)).sheaf 1))
    (hgen : ∀ y : f.fiber x, ∃ t : Line.Bundles.structureModule (f.fiber x) ⟶
      (L.pullback (f.fiberι x)).sheaf, y ∈ Ample.LineBundles.sectionNonvanishing t) :
    ∃ (n : ℕ) (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf)),
      ∀ y : f.fiber x, ∃ i, f.fiberι x y ∈ Ample.LineBundles.sectionNonvanishing (s i) := by
  classical
  have : CompactSpace (f.fiber x) :=
    QuasiCompact.compactSpace_of_compactSpace (f.fiberToSpecResidueField x)
  choose s hs using properFlat_global_sections_cover_fiber f L x hH hgen
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun y => (f.fiberι x ⁻¹ᵁ Ample.LineBundles.sectionNonvanishing (s y) : Set (f.fiber x)))
    (fun y => (f.fiberι x ⁻¹ᵁ Ample.LineBundles.sectionNonvanishing (s y)).isOpen)
    (fun y _ => Set.mem_iUnion.mpr ⟨y, hs y⟩)
  let e := Fintype.equivFin t
  let v : Fin (Fintype.card t + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf) :=
    Fin.lastCases 0 (fun i => s (e.symm i).val)
  refine ⟨Fintype.card t, v, fun y => ?_⟩
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
  change f.fiberι x y ∈ Ample.LineBundles.sectionNonvanishing (s z) at hyz
  refine ⟨(e ⟨z, hz⟩).castSucc, ?_⟩
  have he : (e.symm (e ⟨z, hz⟩)).val = z := congrArg Subtype.val (e.symm_apply_apply ⟨z, hz⟩)
  simpa only [v, Fin.lastCases_castSucc, he] using hyz

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiberSectionGeneration
