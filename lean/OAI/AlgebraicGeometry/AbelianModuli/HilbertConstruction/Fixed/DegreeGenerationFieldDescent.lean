import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.FieldSectionSpanning
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.LinearCombinationNonvanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FieldExtensionReflection

/-! # Degree Generation Field Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Pointwise global generation in a fixed tensor degree descends through
field extensions by the actual flat section base-change map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem Line.Bundles.LineBundle.pointwise_sections_of_fieldExtension
    {K F : Type u} [Field K] [Field F] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [IsProper p] (φ : CommRingCat.of K ⟶ CommRingCat.of F)
    (L : Line.Bundles.LineBundle X)
    (hL : ∀ y : (Limits.pullback p (Spec.map φ) : Scheme.{u}),
      ∃ t : Line.Bundles.structureModule (Limits.pullback p (Spec.map φ)) ⟶
        (L.pullback (pullback.fst p (Spec.map φ))).sheaf, y ∈ Ample.LineBundles.sectionNonvanishing t) :
    ∀ x : X, ∃ s : Line.Bundles.structureModule X ⟶ L.sheaf, x ∈ Ample.LineBundles.sectionNonvanishing s := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have hp : IsSeparated (p ≫ terminal.from (Spec (.of K))) := inferInstance
  have : IsSeparated (terminal.from X) := (terminal.comp_from p) ▸ hp
  have : Surjective (Spec.map φ) := Smooth.FieldExtensionReflection.fieldSpecMap_surjective φ
  let := ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)).toField
  have : Module.Flat Γ(Spec (.of K), ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra (Spec.map φ)) := inferInstance
  let a := pullback.fst p (Spec.map φ)
  let b := pullback.snd p (Spec.map φ)
  intro x
  obtain ⟨y, hy⟩ := a.surjective x
  obtain ⟨t, ht⟩ := hL y
  obtain ⟨n, c, s, he⟩ := HilbertConstruction.Flat.FieldSectionSpanning.flat_fieldPullback_sections_spanned
    (IsPullback.of_hasPullback p (Spec.map φ)) L t
  have hsum : y ∈ Ample.LineBundles.sectionNonvanishing
      (∑ i, Coefficient.ScalarSections.coefficientScalarSection b (c i) (Ample.LineBundles.pullbackSection a (s i))) :=
    (congrArg (fun v => y ∈ Ample.LineBundles.sectionNonvanishing v) he).mp ht
  obtain ⟨i, _, hi⟩ := Section.LinearCombinationNonvanishing.pulledBack_linearCombination_nonvanishing a b L Finset.univ c s y hsum
  exact ⟨s i, hy ▸ hi⟩

theorem Line.Bundles.LineBundle.finite_section_cover_of_pointwise {X : Scheme.{u}} [CompactSpace X]
    (L : Line.Bundles.LineBundle X)
    (h : ∀ x : X, ∃ s : Line.Bundles.structureModule X ⟶ L.sheaf, x ∈ Ample.LineBundles.sectionNonvanishing s) :
    ∃ (n : ℕ) (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf)),
      ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i) := by
  classical
  choose s hs using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (Ample.LineBundles.sectionNonvanishing (s x) : Set X))
    (fun x => (Ample.LineBundles.sectionNonvanishing (s x)).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hs x⟩)
  let e := Fintype.equivFin t
  let v : Fin (Fintype.card t + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf) :=
    Fin.lastCases 0 (fun i => s (e.symm i).val)
  refine ⟨Fintype.card t, v, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  refine ⟨(e ⟨y, hy⟩).castSucc, ?_⟩
  have he : (e.symm (e ⟨y, hy⟩)).val = y := congrArg Subtype.val (e.symm_apply_apply ⟨y, hy⟩)
  simpa only [v, Fin.lastCases_castSucc, he, SetLike.mem_coe] using hxy

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
