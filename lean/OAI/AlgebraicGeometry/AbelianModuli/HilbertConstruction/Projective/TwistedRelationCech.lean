import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorEquivalenceCoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.RelationCechSequence

/-! # Twisted Relation Cech -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective

noncomputable section

/-! Tensoring the constructed projective relation sequence with any line bundle yields an actual short exact sequence of coordinate Čech complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ}
    {I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)} {M : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules}

theorem NegativeTwistCover.ProjectiveNegativeTwistCover.twistedRelationCech_shortExact (D : NegativeTwistCover.ProjectiveNegativeTwistCover I M)
    [M.IsQuasicoherent] (L : Line.Bundles.LineBundle (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))) :
    ((D.relationSequence.map (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence L).functor).map
      (CoefficientCechFunctor.projectiveCoefficientCechFunctor I)).ShortExact := by
  let F := (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence L).functor
  let S : ShortComplex (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules := D.relationSequence.map F
  have h₁ : (D.relationSequence.map F).X₁.IsQuasicoherent :=
    @LineBundle.TensorEquivalenceCoherence.lineBundleRightTensor_quasicoherent _ L D.relations
      (@NegativeTwistCover.ProjectiveNegativeTwistCover.relations_quasicoherent R _ n I M D ‹M.IsQuasicoherent›)
  have h₂ : (D.relationSequence.map F).X₂.IsQuasicoherent :=
    @LineBundle.TensorEquivalenceCoherence.lineBundleRightTensor_quasicoherent _ L D.source D.source_quasicoherent
  have h₃ : (D.relationSequence.map F).X₃.IsQuasicoherent :=
    LineBundle.TensorEquivalenceCoherence.lineBundleRightTensor_quasicoherent L M
  exact @CoefficientCechExactness.projectiveCoefficientCech_shortExact R _ n I S
    (LineBundle.TensorExactness.lineBundleRightTensor_shortExact L D.relationSequence D.relationSequence_shortExact) h₁ h₂ h₃

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective
