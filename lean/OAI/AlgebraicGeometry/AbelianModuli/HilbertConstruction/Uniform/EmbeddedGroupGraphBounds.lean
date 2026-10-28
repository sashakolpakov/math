import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangedGroupGraph
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.EmbeddingField
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InversionGraph

/-! # Embedded Group Graph Bounds -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.EmbeddedGroupGraphBounds.PolarizedAbelianWithLevel

noncomputable section

/-! Addition and inversion in the original native projective
presentations satisfy their full relative Hilbert conditions, quantified
over all field-valued points of an arbitrary tame base. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphProductFlat {S : Scheme.{u}} (X Y : Over S) [Flat X.hom] [Flat Y.hom] :
    Flat (X ⊗ Y).hom := inferInstanceAs (Flat (pullback.fst X.hom Y.hom ≫ X.hom))

local instance _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphProductFinitePresentation {S : Scheme.{u}} (X Y : Over S)
    [LocallyOfFinitePresentation X.hom] [LocallyOfFinitePresentation Y.hom] :
    LocallyOfFinitePresentation (X ⊗ Y).hom := inferInstanceAs
      (LocallyOfFinitePresentation (pullback.fst X.hom Y.hom ≫ X.hom))

private theorem sectionData_cartesian_fiberHilbert_iff
    {S : Scheme.{u}} {X : Over S} [Flat X.hom] [LocallyOfFinitePresentation X.hom]
    {P : Projective.ProjectivePresentations.ProjectivePresentation X} {L : Line.Bundles.LineBundle X.left} (D : P.SectionData L)
    {K : Type u} [Field K] (x : Spec (.of K) ⟶ S) (Y : Over (Spec (.of K)))
    (a : Y.left ⟶ X.left) (H : IsPullback a Y.hom X.hom x) (M : Line.Bundles.LineBundle Y.left)
    (e : (L.pullback a).sheaf ≅ M.sheaf) (poly : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial ((Closed.Families.FlatClosedFamily.ofEmbedding P.embedding).affineProjectivePullback x).homogeneousIdeal.toIdeal poly ↔
      M.HasSectionHilbertPolynomial Y.hom poly :=
  Cartesian.EmbeddingField.relativeEmbedding_fieldHilbert_cartesian_iff P.embedding x Y a H M
    ((Scheme.Modules.pullback a).mapIso D.twistingIso ≪≫ e) poly

private theorem graphHilbert_of_cartesianSectionData
    {S : Scheme.{u}} {X Y : Over S}
    [Flat X.hom] [LocallyOfFinitePresentation X.hom] [IsSeparated Y.hom]
    (P : Projective.ProjectivePresentations.ProjectivePresentation X) (Q : Projective.ProjectivePresentations.ProjectivePresentation Y) (p : X ⟶ Y)
    {L : Line.Bundles.LineBundle X.left} (D : (P.graph Q p).SectionData L) (poly : Polynomial ℚ)
    (hf : ∀ (K : Type u) [Field K] (x : Spec (.of K) ⟶ S),
      ∃ (Z : Over (Spec (.of K))) (a : Z.left ⟶ X.left)
        (_ : IsPullback a Z.hom X.hom x) (M : Line.Bundles.LineBundle Z.left)
        (_ : (L.pullback a).sheaf ≅ M.sheaf), M.HasSectionHilbertPolynomial Z.hom poly) :
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (P.product Q).embedding poly p := by
  let c := MorphismGraphFamilies.familyGraph p ≫ (P.product Q).embedding
  let : IsClosedImmersion c.left := (P.graph Q p).closedImmersion
  have hfamily : (MorphismGraphFamilies.morphismGraphFamily p).reembed (P.product Q).embedding =
      Closed.Families.FlatClosedFamily.ofEmbedding c :=
    Closed.Families.FlatClosedFamily.ofEmbedding_reembed (MorphismGraphFamilies.familyGraph p) (P.product Q).embedding
  intro K _ x
  change HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
    (((MorphismGraphFamilies.morphismGraphFamily p).reembed (P.product Q).embedding).affineProjectivePullback x).homogeneousIdeal.toIdeal _
  rw [hfamily]
  obtain ⟨Z, a, H, M, e, hM⟩ := hf K x
  exact (sectionData_cartesian_fiberHilbert_iff D x Z a H M e poly).mpr hM

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
variable (hg : 0 < g) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
variable (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom)

include hg hN hunit

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.additionGraph_relativePowerEmbedding_hilbertPolynomial :
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial
      ((E.projectivePresentation.product E.projectivePresentation).product E.projectivePresentation).embedding
      ((AdditionGraphPolynomial.normalizedAdditionGraphHilbertPolynomial g δ).comp
        (Polynomial.C (E.degree : ℚ) * Polynomial.X)) μ[A.abelian.scheme] := by
  refine graphHilbert_of_cartesianSectionData (E.projectivePresentation.product E.projectivePresentation)
    E.projectivePresentation μ[A.abelian.scheme] (E.binaryGraphSectionData μ[A.abelian.scheme]) _ ?_
  intro K _ x
  let B := A.pullback x
  let a := Graph.FamilyNaturality.overProductBaseChangeMap x A.abelian.scheme A.abelian.scheme
  let O := A.additionGraphBundle.tensorPower E.degree
  let e : (O.pullback a).sheaf ≅ (B.additionGraphBundle.tensorPower E.degree).sheaf :=
    A.additionGraphBundle.powerBaseChangeIso a E.degree ≪≫
        (TensorPower.Maps.tensorPowerFunctor (B.abelian.scheme ⊗ B.abelian.scheme).left E.degree).mapIso
          (A.additionGraphBundle_baseChangeIso x)
  exact ⟨B.abelian.scheme ⊗ B.abelian.scheme, a,
    Graph.FamilyNaturality.overProductBaseChange_isPullback x A.abelian.scheme A.abelian.scheme,
    B.additionGraphBundle.tensorPower E.degree, e,
      A.pulledBackAdditionGraphBundle_positivePower_hilbertPolynomial_allFields hg hN hunit K x
        E.degree E.degree_pos⟩

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.inversionGraph_relativePowerEmbedding_hilbertPolynomial :
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial
      (E.projectivePresentation.product E.projectivePresentation).embedding
      ((Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ).comp
        (Polynomial.C ((E.degree * 2 : ℕ) : ℚ) * Polynomial.X)) ι[A.abelian.scheme] := by
  refine graphHilbert_of_cartesianSectionData E.projectivePresentation
    E.projectivePresentation ι[A.abelian.scheme] (E.unaryGraphSectionData ι[A.abelian.scheme]) _ ?_
  intro K _ x
  let B := A.pullback x
  let a := pullback.fst A.abelian.scheme.hom x
  let O := A.inversionGraphBundle.tensorPower E.degree
  let e : (O.pullback a).sheaf ≅ (B.inversionGraphBundle.tensorPower E.degree).sheaf :=
    A.inversionGraphBundle.powerBaseChangeIso a E.degree ≪≫
        (TensorPower.Maps.tensorPowerFunctor B.abelian.scheme.left E.degree).mapIso (A.inversionGraphBundle_baseChangeIso x)
  exact ⟨B.abelian.scheme, a, IsPullback.of_hasPullback A.abelian.scheme.hom x,
    B.inversionGraphBundle.tensorPower E.degree, e,
      B.inversionGraphBundle_positivePower_hilbertPolynomial hg hN
        (Geometric.NormalizedGraphPolynomial.fieldPoint_natCast_ne_zero_of_global_unit hunit x) E.degree E.degree_pos⟩

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.uniformEmbeddedGroupGraphBounds (hE : E.degree = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) :
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial
      ((E.projectivePresentation.product E.projectivePresentation).product E.projectivePresentation).embedding
      (Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) μ[A.abelian.scheme] ∧
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (E.projectivePresentation.product E.projectivePresentation).embedding
      (Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ) ι[A.abelian.scheme] := by
  constructor
  · simpa only [Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial, hE] using
      A.additionGraph_relativePowerEmbedding_hilbertPolynomial hg hN hunit E
  · simpa only [Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial, hE] using
      A.inversionGraph_relativePowerEmbedding_hilbertPolynomial hg hN hunit E

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.EmbeddedGroupGraphBounds.PolarizedAbelianWithLevel
