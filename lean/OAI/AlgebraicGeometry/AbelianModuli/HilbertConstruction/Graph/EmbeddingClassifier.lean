import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GraphEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.PointEquivalence

/-! # Embedding Classifier -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.EmbeddingClassifier.PolarizedAbelianWithLevel

noncomputable section

/-! An actual graph-power embedding gives a point of the fixed-dimension
Hilbert parameter. Its classified ideal family recovers the original
abelian scheme over the base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
variable (hg : 0 < g) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
variable (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom)

local instance : Flat (Over.mk A.abelian.scheme.hom).hom :=
  inferInstanceAs (Flat A.abelian.scheme.hom)
local instance : LocallyOfFinitePresentation (Over.mk A.abelian.scheme.hom).hom :=
  inferInstanceAs (LocallyOfFinitePresentation A.abelian.scheme.hom)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEmbeddingHilbertSchemeIso :
    A.abelian.scheme ≅ (A.graphPowerEmbeddingHilbertFamily hg hN hunit E).family.scheme := by
  letI : IsClosedImmersion
    (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom E.sections E.covers).left := E.closedImmersion
  exact Closed.Families.FlatClosedFamily.ofEmbeddingIso
    (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom E.sections E.covers)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEmbeddingHilbertFamily_dimension :
    SmoothOfRelativeDimension g
      (A.graphPowerEmbeddingHilbertFamily hg hN hunit E).family.scheme.hom := by
  let e := A.graphPowerEmbeddingHilbertSchemeIso hg hN hunit E
  let : IsIso e.inv.left := (Over.forget S).map_isIso e.inv
  have h : SmoothOfRelativeDimension (0 + g) (e.inv.left ≫ A.abelian.scheme.hom) :=
    inferInstance
  have h' : SmoothOfRelativeDimension g (e.inv.left ≫ A.abelian.scheme.hom) := by
    simpa only [Nat.zero_add] using h
  exact (congrArg (SmoothOfRelativeDimension g) e.inv.w).mp h'

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEmbeddingFixedDimensionHilbertFamily :
    FixedDimension.Parameters.FixedDimensionRelativeProjectiveHilbertFamily S E.dimension
      ((Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ).comp (Polynomial.C (E.degree : ℚ) * Polynomial.X)) g :=
  ⟨A.graphPowerEmbeddingHilbertFamily hg hN hunit E,
    A.graphPowerEmbeddingHilbertFamily_dimension hg hN hunit E⟩

variable {B : Scheme.{u}} (b : S ⟶ B)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEmbeddingHilbertClassifier :
    Over.mk b ⟶ FixedDimension.Parameters.fixedDimensionHilbertParameter B E.dimension
      ((Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ).comp (Polynomial.C (E.degree : ℚ) * Polynomial.X)) g :=
  (FixedDimension.PointEquivalence.fixedDimensionHilbertParameterPointEquiv B (Over.mk b) E.dimension _ g).symm
    (A.graphPowerEmbeddingFixedDimensionHilbertFamily hg hN hunit E)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEmbeddingHilbertClassifier_classifies :
    (FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily B E.dimension
      ((Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ).comp (Polynomial.C (E.degree : ℚ) * Polynomial.X)) g).pullback (A.graphPowerEmbeddingHilbertClassifier hg hN hunit E b).left =
      A.graphPowerEmbeddingHilbertFamily hg hN hunit E :=
  (FixedDimension.PointEquivalence.fixedDimensionHilbertUniversalFamily_point B (Over.mk b) E.dimension _ g
    (A.graphPowerEmbeddingHilbertClassifier hg hN hunit E b)).trans
      (congrArg Subtype.val ((FixedDimension.PointEquivalence.fixedDimensionHilbertParameterPointEquiv B (Over.mk b)
        E.dimension _ g).apply_symm_apply
          (A.graphPowerEmbeddingFixedDimensionHilbertFamily hg hN hunit E)))

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEmbeddingHilbertClassifier_familyIso :
    A.abelian.scheme ≅
      ((FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily B E.dimension
        ((Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ).comp (Polynomial.C (E.degree : ℚ) * Polynomial.X)) g).pullback (A.graphPowerEmbeddingHilbertClassifier hg hN hunit E b).left).family.scheme :=
  A.graphPowerEmbeddingHilbertSchemeIso hg hN hunit E ≪≫
    eqToIso (congrArg (fun F : RelativeProjective.Families.RelativeProjectiveHilbertFamily S E.dimension
      ((Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ).comp (Polynomial.C (E.degree : ℚ) * Polynomial.X)) =>
        F.family.scheme) (A.graphPowerEmbeddingHilbertClassifier_classifies hg hN hunit E b).symm)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEmbeddingHilbertClassifier_unique
    (c : Over.mk b ⟶ FixedDimension.Parameters.fixedDimensionHilbertParameter B E.dimension
      ((Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ).comp (Polynomial.C (E.degree : ℚ) * Polynomial.X)) g)
    (hc : (FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily B E.dimension
      ((Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ).comp (Polynomial.C (E.degree : ℚ) * Polynomial.X)) g).pullback c.left = A.graphPowerEmbeddingHilbertFamily hg hN hunit E) :
    c = A.graphPowerEmbeddingHilbertClassifier hg hN hunit E b := by
  apply (FixedDimension.PointEquivalence.fixedDimensionHilbertParameterPointEquiv B (Over.mk b) E.dimension _ g).injective
  apply Subtype.ext
  have h0 := FixedDimension.PointEquivalence.fixedDimensionHilbertUniversalFamily_point B (Over.mk b) E.dimension _ g c
  have h1 := A.graphPowerEmbeddingHilbertClassifier_classifies hg hN hunit E b
  have h2 := FixedDimension.PointEquivalence.fixedDimensionHilbertUniversalFamily_point B (Over.mk b) E.dimension _ g
    (A.graphPowerEmbeddingHilbertClassifier hg hN hunit E b)
  exact (h0.symm.trans hc).trans (h1.symm.trans h2)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.EmbeddingClassifier.PolarizedAbelianWithLevel
