import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.NonzeroSection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.OppositeTranslations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OppositeTranslateOpenPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReducedSectionNonvanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionNonvanishing

/-! # Square Generation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! At tame full level, the square of the original graph bundle is globally
generated over an algebraically closed field. Opposite translates construct the sections. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] [IsAlgClosed K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_square_pointwise_sections (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    ∀ x : A.abelian.scheme.left,
      ∃ t : Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower 2).sheaf,
        x ∈ Ample.LineBundles.sectionNonvanishing t := by
  have : IsReduced A.abelian.scheme.left := A.abelian.reduced_overField
  have : JacobsonSpace A.abelian.scheme.left := LocallyOfFiniteType.jacobsonSpace A.abelian.scheme.hom
  obtain ⟨s, hs⟩ := A.graphBundle_exists_nonzero_section hN hNk
  have hU : (Ample.LineBundles.sectionNonvanishing s : Set A.abelian.scheme.left).Nonempty :=
    A.graphBundle.exists_nonvanishing_of_ne_zero s hs
  apply Closed.PointSectionGeneration.lineBundle_pointwise_sections_of_closedPoints (A.graphBundle.tensorPower 2)
  intro x hx
  let b : 𝟙_ (Over (Spec (.of K))) ⟶ A.abelian.scheme :=
    Over.homMk (pointOfClosedPoint A.abelian.scheme.hom x hx)
      (pointOfClosedPoint_comp A.abelian.scheme.hom x hx)
  have hb : b.left (IsLocalRing.closedPoint K) = x :=
    pointOfClosedPoint_apply A.abelian.scheme.hom x hx _
  obtain ⟨a, ha, hai⟩ := A.abelian.exists_oppositeTranslations_mem_open (Ample.LineBundles.sectionNonvanishing s) hU b
  have ha' : (A.abelian.basePointTranslation a).left x ∈ Ample.LineBundles.sectionNonvanishing s := by
    simpa only [hb] using ha
  have hai' : (A.abelian.basePointTranslation a⁻¹).left x ∈ Ample.LineBundles.sectionNonvanishing s := by
    simpa only [hb] using hai
  let f := (A.abelian.basePointTranslation a).left
  let fi := (A.abelian.basePointTranslation a⁻¹).left
  have : IsIso f := ((Over.forget _).mapIso (A.abelian.basePointTranslationIso a)).isIso_hom
  have : IsIso fi := ((Over.forget _).mapIso (A.abelian.basePointTranslationIso a⁻¹)).isIso_hom
  let t := Tensor.ProductSections.tensorProductSection (Ample.LineBundles.pullbackSection f s) (Ample.LineBundles.pullbackSection fi s)
  let e : ((A.graphBundle.pullback f).tensor (A.graphBundle.pullback fi)).sheaf ≅
      (A.graphBundle.tensorPower 2).sheaf :=
    Graph.OppositeTranslations.poincareGraphOppositeTranslationsIso A.dual A.polarization.isogeny.hom a
  refine ⟨t ≫ e.hom, ?_⟩
  erw [Ample.Powers.sectionNonvanishing_comp_iso]
  change x ∈ Ample.LineBundles.sectionNonvanishing
    (Tensor.ProductSections.tensorProductSection (Ample.LineBundles.pullbackSection f s) (Ample.LineBundles.pullbackSection fi s))
  rw [Tensor.SectionNonvanishing.sectionNonvanishing_tensorProduct (A.graphBundle.pullback f) (A.graphBundle.pullback fi),
    Section.Nonvanishing.sectionNonvanishing_pullback, Section.Nonvanishing.sectionNonvanishing_pullback]
  exact ⟨ha', hai'⟩

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_square_finite_section_cover (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    ∃ (n : ℕ) (s : Fin (n + 1) →
      (Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower 2).sheaf)),
      ∀ x : A.abelian.scheme.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i) := by
  classical
  have : CompactSpace A.abelian.scheme.left :=
    QuasiCompact.compactSpace_of_compactSpace A.abelian.scheme.hom
  choose s hs using A.graphBundle_square_pointwise_sections hN hNk
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (Ample.LineBundles.sectionNonvanishing (s x) : Set A.abelian.scheme.left))
    (fun x => (Ample.LineBundles.sectionNonvanishing (s x)).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hs x⟩)
  let e := Fintype.equivFin t
  let v : Fin (Fintype.card t + 1) →
      (Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower 2).sheaf) :=
    Fin.lastCases 0 (fun i => s (e.symm i).val)
  refine ⟨Fintype.card t, v, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  refine ⟨(e ⟨y, hy⟩).castSucc, ?_⟩
  have he : (e.symm (e ⟨y, hy⟩)).val = y := congrArg Subtype.val (e.symm_apply_apply ⟨y, hy⟩)
  simpa only [v, Fin.lastCases_castSucc, he] using
    (show x ∈ Ample.LineBundles.sectionNonvanishing (s y) from hxy)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
