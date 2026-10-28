import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BaseBasisEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.SectionBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveTargetIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ClosedOf

/-! # Basis Embedding Field Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BasisEmbeddingFieldCriterion

noncomputable section

/-! A finite map defined by a complete section basis over an affine spectrum
is a closed immersion when its section comparisons and power factorizations
hold on every field-valued fiber. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem affine_basis_sectionMap_closedImmersion_of_field_factorizations
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (L : Line.Bundles.LineBundle X) {n : ℕ}
    (B : Module.Basis (Fin (n + 1)) Γ(Spec (.of R), ⊤)
      ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor f.appTop.hom).obj L.sheaf))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (Coefficient.RingSectionBasis.coefficientRingBasisFamily f.appTop.hom L.sheaf B i))
    [IsFinite (SectionsProjectiveMorphism.sectionProjectiveMorphism f (Coefficient.RingSectionBasis.coefficientRingBasisFamily f.appTop.hom L.sheaf B) hs).left]
    (hBC : ∀ (K : Type u) [Field K] (b : Spec (.of K) ⟶ Spec (.of R)),
      Function.Bijective ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison (IsPullback.of_hasPullback f b) L.sheaf).app (.op ⊤)))
    (hfactor : ∀ (K : Type u) [Field K] (b : Spec (.of K) ⟶ Spec (.of R))
      (m : ℕ), 0 < m → Section.FactorizationSpans.SectionFactorizationSpan (Line.Bundles.structureModule (pullback f b))
        (((L.pullback (pullback.fst f b)).tensorPower m).sheaf)
        (((L.pullback (pullback.fst f b)).tensorPower (1 + m)).sheaf)) :
    IsClosedImmersion (SectionsProjectiveMorphism.sectionProjectiveMorphism f (Coefficient.RingSectionBasis.coefficientRingBasisFamily f.appTop.hom L.sheaf B) hs).left := by
  let s := Coefficient.RingSectionBasis.coefficientRingBasisFamily f.appTop.hom L.sheaf B
  let j := SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs
  apply Finite.ClosedOf.finite_overMap_closedImmersion_of_field_baseChanges R j
  intro K _ _
  let b := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let a := pullback.fst f b
  let q := pullback.snd f b
  let H := IsPullback.of_hasPullback f b
  let LK := L.pullback a
  let BK := Cartesian.SectionBasis.cartesianSectionBasis H L.sheaf (hBC K b) B
  let t := Coefficient.RingSectionBasis.coefficientRingBasisFamily q.appTop.hom LK.sheaf BK
  have ht : ∀ y : (pullback f b : Scheme.{u}), ∃ i, y ∈ Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection a (s i)) :=
    Section.ChartArbitraryPullback.lineBundleSections_pullback_covers a L s hs
  have het : t = fun i => Ample.LineBundles.pullbackSection a (s i) :=
    funext (Cartesian.SectionBasis.cartesianSectionBasis_family H L.sheaf (hBC K b) B)
  have htB : ∀ y : (pullback f b : Scheme.{u}), ∃ i, y ∈ Ample.LineBundles.sectionNonvanishing (t i) := het.symm ▸ ht
  let jK := SectionsProjectiveMorphism.sectionProjectiveMorphism q (fun i => Ample.LineBundles.pullbackSection a (s i)) ht
  have HJ : IsPullback a jK.left j.left (RelativeProjective.BaseMaps.relativeProjectiveBaseMap b n) :=
    Section.ProjectiveBaseChange.sectionProjectiveMorphism_isPullback a b f q H L s hs ht
  have : IsFinite jK.left := MorphismProperty.of_isPullback HJ inferInstance
  have hej : SectionsProjectiveMorphism.sectionProjectiveMorphism q t htB = jK :=
    Section.ProjectiveTargetIso.sectionProjectiveMorphism_congr q het htB ht
  have : IsFinite (SectionsProjectiveMorphism.sectionProjectiveMorphism q t htB).left := hej.symm ▸ inferInstance
  have : IsProper q := inferInstance
  have : CompactSpace (pullback f b : Scheme.{u}) := QuasiCompact.compactSpace_of_compactSpace q
  have : (pullback f b).IsSeparated := ⟨by rw [← terminal.comp_from q]; infer_instance⟩
  have hcB : IsClosedImmersion (SectionsProjectiveMorphism.sectionProjectiveMorphism q t htB).left :=
    BaseBasisEmbedding.coefficientRingBasisFamily_closedImmersion_of_finite q LK BK (hfactor K b) htB
  have : IsClosedImmersion jK.left := hej ▸ hcB
  let HP := RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback b n
  have he : jK.left ≫ HP.isoPullback.hom = ((Over.pullback b).map j).left := by
    apply pullback.hom_ext
    · rw [Category.assoc, HP.isoPullback_hom_fst, ← HJ.w]
      simp only [Over.pullback_map_left, pullback.lift_fst]
      rfl
    · rw [Category.assoc, HP.isoPullback_hom_snd, SectionsProjectiveMorphism.sectionProjectiveMorphism_over]
      simp only [Over.pullback_map_left, pullback.lift_snd]
      rfl
  have hc : IsClosedImmersion (jK.left ≫ HP.isoPullback.hom) := inferInstance
  exact he ▸ hc

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BasisEmbeddingFieldCriterion
