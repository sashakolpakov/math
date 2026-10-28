import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.BaseChangeEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.FamilyGroupOperations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ClosedFamilyIntrinsicPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.Family

/-! # Classifier Intrinsic Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ClassifierIntrinsicRecovery.PolarizedAbelianWithLevel

noncomputable section

/-! The Hilbert classifier of a graph-power embedding recovers the native
pullback of the universal family, with exact compatibility of the original
projective embedding. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option cleanup.letToHave false
private theorem isoComposite_embedding
    {C : Type*} [Category C] {X Y Z W : C}
    (a : X ≅ Y) (b : Y ≅ Z) (j : Z ⟶ W) (k : Y ⟶ W) (r : X ⟶ W)
    (hb : b.hom ≫ j = k) (ha : a.hom ≫ k = r) :
    (a ≪≫ b).hom ≫ j = r := by
  rw [Iso.trans_hom, Category.assoc, hb, ha]

private theorem familyIso_embedding_comp
    {S : Scheme.{u}} {n : ℕ} {poly : Polynomial ℚ} {X : Over S}
    (F G : RelativeProjective.Families.RelativeProjectiveHilbertFamily S n poly) (e : X ≅ F.family.scheme)
    (h : F = G) (j : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) (he : e.hom ≫ F.family.inclusion = j) :
    (e ≪≫ eqToIso (congrArg (fun H : RelativeProjective.Families.RelativeProjectiveHilbertFamily S n poly => H.family.scheme) h)).hom ≫
      G.family.inclusion = j := by
  cases h
  simpa using he

private theorem nativePullback_embedding_comp
    {B S : Scheme.{u}} {n : ℕ} {X : Over S}
    (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver B n)) (c : S ⟶ B)
    (e : X ≅ (F.projectiveBaseChange c).scheme) (j : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n)
    (he : e.hom ≫ (F.projectiveBaseChange c).inclusion = j) :
    (e ≪≫ F.projectiveBaseChangeSchemeIso c).hom ≫
      CategoryTheory.Functors.FunctorReturnIsomorphism.functorReturnMap (Over.pullback c) F.inclusion
        (Projective.SpaceBaseChange.projectiveSpaceOverBaseChangeIso c n) = j := by
  exact isoComposite_embedding e (F.projectiveBaseChangeSchemeIso c)
    (CategoryTheory.Functors.FunctorReturnIsomorphism.functorReturnMap (Over.pullback c) F.inclusion
      (Projective.SpaceBaseChange.projectiveSpaceOverBaseChangeIso c n))
    (F.projectiveBaseChange c).inclusion j
    (F.projectiveBaseChangeSchemeIso_embedding c) he

variable {S B : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
variable (hg : 0 < g) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
variable (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom) (b : S ⟶ B)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEmbeddingHilbertClassifier_familyIso_embedding :
    (A.graphPowerEmbeddingHilbertClassifier_familyIso hg hN hunit E b).hom ≫
      ((FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily B E.dimension
        ((Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ).comp (Polynomial.C (E.degree : ℚ) * Polynomial.X)) g).pullback (A.graphPowerEmbeddingHilbertClassifier hg hN hunit E b).left).family.inclusion =
      E.projectivePresentation.embedding := by
  exact familyIso_embedding_comp _ _
    (A.graphPowerEmbeddingHilbertSchemeIso hg hN hunit E)
    (A.graphPowerEmbeddingHilbertClassifier_classifies hg hN hunit E b).symm
    E.projectivePresentation.embedding
    (A.graphPowerEmbeddingHilbertSchemeIso_embedding hg hN hunit E)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEmbeddingHilbertClassifier_nativeFamilyIso :
    A.abelian.scheme ≅
      (Over.pullback (A.graphPowerEmbeddingHilbertClassifier hg hN hunit E b).left).obj
        (FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily B E.dimension
          ((Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ).comp (Polynomial.C (E.degree : ℚ) * Polynomial.X)) g).family.scheme :=
  A.graphPowerEmbeddingHilbertClassifier_familyIso hg hN hunit E b ≪≫
    (FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily B E.dimension
      ((Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ).comp (Polynomial.C (E.degree : ℚ) * Polynomial.X)) g).family.projectiveBaseChangeSchemeIso (A.graphPowerEmbeddingHilbertClassifier hg hN hunit E b).left

abbrev _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEmbeddingHilbertClassifier_nativeFamilyIso_embedding :=
  nativePullback_embedding_comp
    (FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily B E.dimension
      ((Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ).comp (Polynomial.C (E.degree : ℚ) * Polynomial.X)) g).family
    (A.graphPowerEmbeddingHilbertClassifier hg hN hunit E b).left
    (A.graphPowerEmbeddingHilbertClassifier_familyIso hg hN hunit E b)
    E.projectivePresentation.embedding
    (A.graphPowerEmbeddingHilbertClassifier_familyIso_embedding hg hN hunit E b)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ClassifierIntrinsicRecovery.PolarizedAbelianWithLevel
