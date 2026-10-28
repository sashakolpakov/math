import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.EmbeddingFieldCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GeometricGraphEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.Families

/-! # Graph Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GraphEmbedding.PolarizedAbelianWithLevel

noncomputable section

/-! Every actual graph-power embedding over an arbitrary tame base has the
polarization-type Hilbert polynomial on every field-valued fiber. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

local instance : Flat (Over.mk A.abelian.scheme.hom).hom :=
  inferInstanceAs (Flat A.abelian.scheme.hom)
local instance : LocallyOfFinitePresentation (Over.mk A.abelian.scheme.hom).hom :=
  inferInstanceAs (LocallyOfFinitePresentation A.abelian.scheme.hom)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_relativePowerEmbedding_hilbertPolynomial
    (hg : 0 < g) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom) :
    letI : IsClosedImmersion
      (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom E.sections E.covers).left := E.closedImmersion
    ∀ (K : Type u) [Field K] (x : Spec (.of K) ⟶ S),
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial ((Closed.Families.FlatClosedFamily.ofEmbedding
        (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom E.sections E.covers)).affineProjectivePullback x).homogeneousIdeal.toIdeal ((Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ).comp
          (Polynomial.C (E.degree : ℚ) * Polynomial.X)) := by
  let : IsClosedImmersion
    (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom E.sections E.covers).left := E.closedImmersion
  intro K _ x
  let B := A.pullback x
  let a := CategoryTheory.Limits.pullback.fst A.abelian.scheme.hom x
  let M := (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S E.dimension).pullback
    (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom E.sections E.covers).left
  let e₀ : M.sheaf ≅ (A.graphBundle.tensorPower E.degree).sheaf :=
    E.twistingBundleIso A.abelian.scheme.hom ≪≫
      (E.isPower.unique (A.graphBundle.tensorPower_isTensorPower E.degree)).some
  let e : (M.pullback a).sheaf ≅ (B.graphBundle.tensorPower E.degree).sheaf :=
    (Scheme.Modules.pullback a).mapIso e₀ ≪≫ A.graphBundle.powerBaseChangeIso a E.degree ≪≫
      (TensorPower.Maps.tensorPowerFunctor B.abelian.scheme.left E.degree).mapIso (A.graphBundle_baseChangeIso x).symm
  apply (EmbeddingFieldCriterion.relativeEmbedding_fieldHilbert_iff
    (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom E.sections E.covers) x _).mpr
  exact (Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_sheafIso B.abelian.scheme.hom
    (M.pullback a) (B.graphBundle.tensorPower E.degree) e _).mpr
      (B.graphBundle_positivePower_normalized_hilbertPolynomial hg hN
        (Geometric.NormalizedGraphPolynomial.fieldPoint_natCast_ne_zero_of_global_unit hunit x) E.degree E.degree_pos)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEmbeddingHilbertFamily
    (hg : 0 < g) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom) :
    RelativeProjective.Families.RelativeProjectiveHilbertFamily S E.dimension
      ((Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ).comp (Polynomial.C (E.degree : ℚ) * Polynomial.X)) := by
  letI : IsClosedImmersion
    (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom E.sections E.covers).left := E.closedImmersion
  exact ⟨Closed.Families.FlatClosedFamily.ofEmbedding
    (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom E.sections E.covers),
      A.graphBundle_relativePowerEmbedding_hilbertPolynomial hg hN hunit E⟩

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphPowerEmbeddingHilbertFamily
    (hg : 0 < g) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom)
    (hE : E.degree = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) :
    RelativeProjective.Families.RelativeProjectiveHilbertFamily S E.dimension (Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) := by
  simpa only [Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial, hE] using
    A.graphPowerEmbeddingHilbertFamily hg hN hunit E

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GraphEmbedding.PolarizedAbelianWithLevel
