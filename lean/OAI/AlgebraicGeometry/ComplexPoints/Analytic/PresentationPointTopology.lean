import OAI.AlgebraicGeometry.Foundations.Scheme.PresentationComplexPoints
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.QuotientPointTopology

/-! # Presentation Point Topology -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.PresentationPointTopology

noncomputable section

/-!
# Ordinary topology of polynomial presentations

Complex points of a polynomial quotient are homeomorphic to the actual common
zero set of its defining ideal, with the ordinary coordinate topology. The
same assertion holds for a specified family of polynomial equations. For
finitely many variables, these are closed subspaces of complex affine space
with its Euclidean topology.
-/

universe u v

variable {σ : Type u} {κ : Type v}

/-- Polynomial coordinates identify the two ordinary topologies on an ideal zero locus. -/
def polynomialIdealZeroLocusHomeomorph (I : Ideal (MvPolynomial σ ℂ)) :
    Foundations.Scheme.QuotientComplexPoints.affineIdealZeroLocus I ≃ₜ MvPolynomial.zeroLocus ℂ I where
  toEquiv := Foundations.Scheme.PresentationComplexPoints.polynomialIdealZeroLocusEquiv I
  continuous_toFun :=
    ((PolynomialEvaluation.polynomialPointHomeomorph σ).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((PolynomialEvaluation.polynomialPointHomeomorph σ).symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- Complex points of a polynomial quotient are its ordinary coordinate zero locus. -/
def presentationComplexPointsHomeomorph (I : Ideal (MvPolynomial σ ℂ)) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial σ ℂ ⧸ I) ≃ₜ MvPolynomial.zeroLocus ℂ I :=
  (QuotientPointTopology.quotientComplexPointsHomeomorph I).trans (polynomialIdealZeroLocusHomeomorph I)

/-- The homeomorphism is the already-constructed algebraic presentation bijection. -/
@[simp]
theorem presentationComplexPointsHomeomorph_toEquiv (I : Ideal (MvPolynomial σ ℂ)) :
    (presentationComplexPointsHomeomorph I).toEquiv = Foundations.Scheme.PresentationComplexPoints.presentationComplexPointsEquiv I := rfl

/-- Its coordinates evaluate the residue classes of the polynomial variables. -/
@[simp]
theorem presentationComplexPointsHomeomorph_apply (I : Ideal (MvPolynomial σ ℂ))
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial σ ℂ ⧸ I)) (i : σ) :
    (presentationComplexPointsHomeomorph I x).val i =
      x (Ideal.Quotient.mk I (MvPolynomial.X i)) := rfl

/-- Evaluation of any polynomial agrees with evaluation of its quotient class. -/
@[simp]
theorem presentationComplexPointsHomeomorph_eval (I : Ideal (MvPolynomial σ ℂ))
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial σ ℂ ⧸ I)) (p : MvPolynomial σ ℂ) :
    MvPolynomial.eval (presentationComplexPointsHomeomorph I x).val p =
      x (Ideal.Quotient.mk I p) :=
  Foundations.Scheme.PresentationComplexPoints.presentationComplexPointsEquiv_eval I x p

/-- The presentation coordinate map is a closed embedding in ordinary affine space. -/
theorem isClosedEmbedding_presentationCoordinates (I : Ideal (MvPolynomial σ ℂ)) :
    Topology.IsClosedEmbedding (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial σ ℂ ⧸ I) =>
      (presentationComplexPointsHomeomorph I x).val) :=
  (PolynomialZeroLocus.isClosed_mvPolynomial_zeroLocus I).isClosedEmbedding_subtypeVal.comp
    (presentationComplexPointsHomeomorph I).isClosedEmbedding

/-- Generating an ideal from equations does not change the subspace topology. -/
def relationsZeroLocusHomeomorph (F : κ → MvPolynomial σ ℂ) :
    MvPolynomial.zeroLocus ℂ (Ideal.span (Set.range F)) ≃ₜ
      {z : σ → ℂ // ∀ j, MvPolynomial.eval z (F j) = 0} where
  toEquiv := Foundations.Scheme.PresentationComplexPoints.relationsZeroLocusEquiv F
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

/-- The ordinary point space of an algebra given by equations is their solution space. -/
def equationsComplexPointsHomeomorph (F : κ → MvPolynomial σ ℂ) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial σ ℂ ⧸ Ideal.span (Set.range F)) ≃ₜ
      {z : σ → ℂ // ∀ j, MvPolynomial.eval z (F j) = 0} :=
  (presentationComplexPointsHomeomorph (Ideal.span (Set.range F))).trans
    (relationsZeroLocusHomeomorph F)

/-- This homeomorphism retains the actual equation-presentation bijection. -/
@[simp]
theorem equationsComplexPointsHomeomorph_toEquiv (F : κ → MvPolynomial σ ℂ) :
    (equationsComplexPointsHomeomorph F).toEquiv = Foundations.Scheme.PresentationComplexPoints.equationsComplexPointsEquiv F := rfl

/-- The equation-presentation coordinates are the original variable values. -/
@[simp]
theorem equationsComplexPointsHomeomorph_apply (F : κ → MvPolynomial σ ℂ)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial σ ℂ ⧸ Ideal.span (Set.range F))) (i : σ) :
    (equationsComplexPointsHomeomorph F x).val i =
      x (Ideal.Quotient.mk (Ideal.span (Set.range F)) (MvPolynomial.X i)) := rfl

/-- An arbitrary family of polynomial equations has a closed ordinary solution space. -/
theorem isClosed_equationsZeroLocus (F : κ → MvPolynomial σ ℂ) :
    IsClosed {z : σ → ℂ | ∀ j, MvPolynomial.eval z (F j) = 0} := by
  have hset : {z : σ → ℂ | ∀ j, MvPolynomial.eval z (F j) = 0} =
      ⋂ j, {z : σ → ℂ | MvPolynomial.eval z (F j) = 0} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hset]
  exact isClosed_iInter fun j => PolynomialZeroLocus.isClosed_mvPolynomial_zeroSet (F j)

/-- Coordinates of an algebra defined by equations give a closed topological embedding. -/
theorem isClosedEmbedding_equationsCoordinates (F : κ → MvPolynomial σ ℂ) :
    Topology.IsClosedEmbedding
      (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial σ ℂ ⧸ Ideal.span (Set.range F)) =>
        (equationsComplexPointsHomeomorph F x).val) :=
  (isClosed_equationsZeroLocus F).isClosedEmbedding_subtypeVal.comp
    (equationsComplexPointsHomeomorph F).isClosedEmbedding

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.PresentationPointTopology
