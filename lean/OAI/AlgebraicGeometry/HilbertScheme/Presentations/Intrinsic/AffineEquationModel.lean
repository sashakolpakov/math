import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.PolynomialCoefficients
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ImmersionKernelIso
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.HomogeneousCoordinateBaseChange

/-! # Affine Equation Model -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.AffineEquationModel.GradedHilbert

noncomputable section

/-! Finite equations of a native affine family produce an actual model
over a finitely generated coefficient subalgebra. Its extended equations
recover the exact native closed subscheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v
variable {S : Scheme.{u}} {R : Type u} [CommRing R] {n : ℕ}
variable (a : Spec (CommRingCat.of R) ⟶ S)
variable (F : Hilbert.Functor.Family (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a))

structure NativeAffineEquations where
  count : ℕ
  degree : ℕ
  generators : Fin count → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n
  homogeneous : ∀ j, (generators j).IsHomogeneous degree
  realization : (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal generators degree homogeneous) ≫
    (Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).hom).ker = F.val

def nativeAffineEquations : NativeAffineEquations a F := by
  apply Classical.choice
  obtain ⟨m, N, g, hg, he⟩ := SingleDegreeEquations.GradedHilbert.native_affine_single_degree_equations a F
  exact ⟨⟨m, N, g, hg, he⟩⟩

variable {a F} (E : NativeAffineEquations a F) (B : Type v) [CommRing B] [Algebra B R]

abbrev nativeEquationCoefficientRing : Subalgebra B R := Noetherian.PolynomialCoefficients.GradedHilbert.polynomialCoefficientRing E.generators B

def nativeEquationModelIdeal : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading (nativeEquationCoefficientRing E B) n) :=
  Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal (Noetherian.PolynomialCoefficients.GradedHilbert.polynomialOverCoefficientRing E.generators B) E.degree
    (Noetherian.PolynomialCoefficients.GradedHilbert.polynomialOverCoefficientRing_homogeneous E.generators B E.degree E.homogeneous)

def nativeEquationExtendedIdeal : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n) :=
  (nativeEquationModelIdeal E B).map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap (nativeEquationCoefficientRing E B).val.toRingHom)

theorem nativeEquationExtendedIdeal_eq : nativeEquationExtendedIdeal E B =
    Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal E.generators E.degree E.homogeneous :=
  Noetherian.PolynomialCoefficients.GradedHilbert.coefficientRing_generatorsIdeal_map E.generators B E.degree E.homogeneous

theorem nativeEquationModel_realization :
    (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (nativeEquationExtendedIdeal E B) ≫ (Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).hom).ker = F.val := by
  rw [nativeEquationExtendedIdeal_eq]
  exact E.realization

def nativeEquationModelIso : F.val.subscheme ≅ Projective.Quotient.GradedHilbert.projectiveQuotient (nativeEquationExtendedIdeal E B) :=
  Closed.ImmersionKernelIso.closedImmersionKernelIso F.val.subschemeι
    (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (nativeEquationExtendedIdeal E B) ≫ (Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).hom)
    (F.val.ker_subschemeι.trans (nativeEquationModel_realization E B).symm)

theorem nativeEquationModelIso_projection :
    (nativeEquationModelIso E B).hom ≫ Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (nativeEquationExtendedIdeal E B)) =
      Hilbert.Functor.familyProjection (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) F.val := by
  let I := nativeEquationExtendedIdeal E B
  let j : Projective.Quotient.GradedHilbert.projectiveQuotient I ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading R n) := Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I
  have hp : (j ≫ (Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).hom) ≫
      Hilbert.Functor.ambientProjection (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a) =
        Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I) := by
    rw [Category.assoc, Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso_projection]
    exact Projective.QuotientStructure.GradedHilbert.projectiveQuotientInclusion_structure I
  have hi : (nativeEquationModelIso E B).hom ≫ (j ≫ (Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).hom) = F.val.subschemeι :=
    Closed.ImmersionKernelIso.closedImmersionKernelIso_hom _ _ _
  exact (congrArg (fun f => (nativeEquationModelIso E B).hom ≫ f) hp).symm.trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun f => f ≫ Hilbert.Functor.ambientProjection (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)) hi))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.AffineEquationModel.GradedHilbert
