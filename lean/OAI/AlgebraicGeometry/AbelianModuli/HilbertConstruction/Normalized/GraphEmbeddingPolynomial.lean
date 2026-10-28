import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GraphPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.EmbeddingIntrinsic
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.TwistingBundle

/-! # Graph Embedding Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GraphEmbeddingPolynomial.PolarizedAbelianWithLevel

noncomputable section

/-! Each actual graph-power embedding has the specified type polynomial,
including its full Hilbert condition after every extension of the ground field. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

local instance : Flat (Over.mk A.abelian.scheme.hom).hom :=
  inferInstanceAs (Flat A.abelian.scheme.hom)
local instance : LocallyOfFinitePresentation (Over.mk A.abelian.scheme.hom).hom :=
  inferInstanceAs (LocallyOfFinitePresentation A.abelian.scheme.hom)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_powerEmbedding_hilbertPolynomial
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom) :
    letI : IsClosedImmersion
        (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom E.sections E.covers).left := E.closedImmersion
    ∀ (F : Type u) [Field F] (x : Spec (.of F) ⟶ Spec (.of K)),
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial ((Closed.Families.FlatClosedFamily.ofEmbedding
        (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom E.sections E.covers)).affineProjectivePullback x).homogeneousIdeal.toIdeal
          ((GraphPolynomial.normalizedGraphHilbertPolynomial g δ).comp
            (Polynomial.C (E.degree : ℚ) * Polynomial.X)) := by
  let : IsClosedImmersion
      (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom E.sections E.covers).left := E.closedImmersion
  have : Flat (Over.mk A.abelian.scheme.hom).hom := inferInstanceAs (Flat A.abelian.scheme.hom)
  have : LocallyOfFinitePresentation (Over.mk A.abelian.scheme.hom).hom :=
    inferInstanceAs (LocallyOfFinitePresentation A.abelian.scheme.hom)
  let M := (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of K)) E.dimension).pullback
    (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom E.sections E.covers).left
  let e : M.sheaf ≅ (A.graphBundle.tensorPower E.degree).sheaf :=
    E.twistingBundleIso A.abelian.scheme.hom ≪≫
      (E.isPower.unique (A.graphBundle.tensorPower_isTensorPower E.degree)).some
  apply (Relative.EmbeddingIntrinsic.relativeEmbedding_hilbertPolynomial_iff
    (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom E.sections E.covers) _).mpr
  exact (Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_sheafIso A.abelian.scheme.hom
    M (A.graphBundle.tensorPower E.degree) e _).mpr
      (A.graphBundle_positivePower_normalized_hilbertPolynomial hg hN hNk E.degree E.degree_pos)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GraphEmbeddingPolynomial.PolarizedAbelianWithLevel
