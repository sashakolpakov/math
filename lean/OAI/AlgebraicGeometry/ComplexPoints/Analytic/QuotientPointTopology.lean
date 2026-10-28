import OAI.AlgebraicGeometry.Foundations.Scheme.QuotientComplexPoints
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffinePointMaps
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialZeroLocus

/-! # Quotient Point Topology -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.QuotientPointTopology

/-!
# Quotient algebras and closed spaces of complex points

The algebraic correspondence between characters of `A ⧸ I` and characters of A
vanishing on I is a homeomorphism for their ordinary evaluation topologies.
Consequently the point map of the quotient is a closed topological embedding.
-/

universe u

variable {A : Type u} [CommRing A] [Algebra ℂ A]

/-- An ideal's zero locus is closed in the ordinary topology on affine points. -/
theorem isClosed_affineIdealZeroLocus (I : Ideal A) :
    IsClosed (Foundations.Scheme.QuotientComplexPoints.affineIdealZeroLocus I) :=
  Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosed_commonZeroSet (I : Set A)

/-- The ordinary complex points of a quotient are its closed ideal zero locus. -/
def quotientComplexPointsHomeomorph (I : Ideal A) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⧸ I) ≃ₜ Foundations.Scheme.QuotientComplexPoints.affineIdealZeroLocus I where
  toEquiv := Foundations.Scheme.QuotientComplexPoints.quotientComplexPointsEquiv I
  continuous_toFun :=
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (Ideal.Quotient.mkₐ ℂ I)).continuous.subtype_mk _
  continuous_invFun := by
    apply (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_iff _).mpr
    intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    change Continuous (fun x : Foundations.Scheme.QuotientComplexPoints.affineIdealZeroLocus I => x.val a)
    exact (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval a).comp continuous_subtype_val

/-- The homeomorphism uses the original algebraic quotient-point correspondence. -/
@[simp]
theorem quotientComplexPointsHomeomorph_toEquiv (I : Ideal A) :
    (quotientComplexPointsHomeomorph I).toEquiv = Foundations.Scheme.QuotientComplexPoints.quotientComplexPointsEquiv I := rfl

/-- Its forward map is restriction along the quotient algebra homomorphism. -/
@[simp]
theorem quotientComplexPointsHomeomorph_val (I : Ideal A)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⧸ I)) :
    (quotientComplexPointsHomeomorph I x).val =
      x.comp (Ideal.Quotient.mkₐ ℂ I) := rfl

/-- Its inverse evaluates a quotient class using any representative. -/
@[simp]
theorem quotientComplexPointsHomeomorph_symm_apply_mk (I : Ideal A)
    (x : Foundations.Scheme.QuotientComplexPoints.affineIdealZeroLocus I) (a : A) :
    (quotientComplexPointsHomeomorph I).symm x (Ideal.Quotient.mk I a) = x.val a := rfl

/-- The ordinary point map of an algebra quotient is a closed topological embedding. -/
theorem isClosedEmbedding_quotientComplexPoints_restrict (I : Ideal A) :
    Topology.IsClosedEmbedding (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⧸ I) =>
      x.comp (Ideal.Quotient.mkₐ ℂ I)) :=
  (isClosed_affineIdealZeroLocus I).isClosedEmbedding_subtypeVal.comp
    (quotientComplexPointsHomeomorph I).isClosedEmbedding

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.QuotientPointTopology
