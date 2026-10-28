import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.GraphHilbertBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ScalarExtension

/-! # Projective Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Over a field, the actual Hilbert-polynomial condition on every field-valued fiber is equivalent to the condition on the identity fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ScalarExtension.GradedHilbert

universe u

variable {K : Type u} [Field K] {n : ℕ}

theorem Closed.Families.FlatClosedFamily.coefficientField_hilbertPolynomial_iff
    (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace K n))
    {L : Type u} [Field L] (φ : CommRingCat.of K ⟶ CommRingCat.of L) (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (F.pullbackAlong (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n) (Spec.map φ)
      (Projective.CoefficientFunctoriality.polynomialProjectiveMap_isPullback φ n)).homogeneousIdeal.toIdeal P ↔
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial F.homogeneousIdeal.toIdeal P := by
  let : Algebra K L := φ.hom.toAlgebra
  have he := Closed.Families.FlatClosedFamily.homogeneousIdeal_coefficientBaseChange
    (R := CommRingCat.of K) (A := CommRingCat.of L) (n := n) F φ
  rw [he, HilbertScheme.Presentations.Saturation.Polynomial.GradedHilbert.projectiveSaturation_hasHilbertPolynomial_iff]
  exact HilbertScheme.Presentations.Hilbert.ScalarExtension.GradedHilbert.hasHilbertPolynomial_scalarExtended_iff F.homogeneousIdeal P

theorem Closed.Families.FlatClosedFamily.fieldHilbert_iff_identity
    (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of K)) n)) (P : Polynomial ℚ) :
    (∀ (L : Type u) [Field L] (x : Spec (.of L) ⟶ Spec (.of K)),
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (F.affineProjectivePullback x).homogeneousIdeal.toIdeal P) ↔
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (F.affineProjectivePullback (𝟙 _)).homogeneousIdeal.toIdeal P := by
  constructor
  · intro h
    exact h K (𝟙 _)
  · intro h L _ x
    let φ : CommRingCat.of K ⟶ CommRingCat.of L := (Spec.fullyFaithful.preimage x).unop
    have he : Spec.map φ = x := Spec.fullyFaithful.map_preimage x
    have hx := F.affineProjectivePullback_coefficient (𝟙 _) φ
    have hc : Spec.map φ ≫ 𝟙 (Spec (.of K)) = x := (Category.comp_id _).trans he
    have hF := (congrArg (fun a => F.affineProjectivePullback a) hc).symm.trans hx
    exact (congrArg (fun G : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace L n) =>
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial G.homogeneousIdeal.toIdeal P) hF).mpr
        (((F.affineProjectivePullback (𝟙 _)).coefficientField_hilbertPolynomial_iff φ P).mpr h)

open _root_.CategoryTheory.MonoidalCategory

theorem Field.ProjectiveCriterion.hasEmbeddedGraphHilbertPolynomial_iff_identity
    {A B : Over (Spec (.of K))} [Flat A.hom] [LocallyOfFinitePresentation A.hom] [IsSeparated B.hom]
    (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of K)) n) [IsClosedImmersion j.left]
    (P : Polynomial ℚ) (p : A ⟶ B) :
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P p ↔
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (((MorphismGraphFamilies.morphismGraphFamily p).reembed j).affineProjectivePullback (𝟙 _)).homogeneousIdeal.toIdeal P :=
  ((MorphismGraphFamilies.morphismGraphFamily p).reembed j).fieldHilbert_iff_identity P

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
