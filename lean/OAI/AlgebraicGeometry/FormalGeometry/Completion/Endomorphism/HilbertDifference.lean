import OAI.AlgebraicGeometry.FormalGeometry.Completion.EffectiveHilbertDifference
import OAI.AlgebraicGeometry.FormalGeometry.Completion.GeneratedAmpleBundle
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.ProjectiveEmbedding
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic

/-! # Hilbert Difference -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.HilbertDifference

noncomputable section

/-! An actual polynomial-valued positive invariant of endomorphisms.
The presentation and generated symmetric ample bundle are derived from the native group.
No quadratic numerical identity is asserted for this Hilbert difference. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u

variable {K : Type u} [Field K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]

structure EndomorphismNumericalPresentation where
  projective : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A
  bundle : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left
  ample : bundle.IsAmple
  frames : Frame.SectionDetection.Construction.HasFrameSections bundle.sheaf
  symmetric : Nonempty ((bundle.pullback (GrpObj.inv (X := A)).left).sheaf ≅ bundle.sheaf)

def endomorphismNumericalPresentation [IsAlgClosed K] [IsProper A.hom] [Smooth A.hom]
    [GeometricallyIntegral A.hom] : EndomorphismNumericalPresentation A := by
  apply Classical.choice
  obtain ⟨P⟩ := Geometric.Projectivity.Construction.geometric_group_projectivePresentation A
  obtain ⟨L, hL, hg, hs⟩ := GeneratedAmpleBundle.Construction.exists_symmetric_generated_ample_lineBundle A
  exact ⟨⟨P, L, hL, hg, hs⟩⟩

variable [GeometricallyIntegral A.hom]

def endomorphismHilbertDifference (D : EndomorphismNumericalPresentation A)
    (f : Endomorphisms.Construction.AlgebraicEnd A) : Polynomial ℚ := by
  let : Field Γ(Spec (CommRingCat.of K), ⊤) := Quotients.FiniteDescent.FieldPoint.Construction.FieldPointPrime.sectionsField K
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  exact EffectiveHilbertDifference.Construction.lineBundleHilbertDifference (Affine.ProjectiveEmbedding.Construction.projectiveAffineEmbedding A D.projective)
    (D.bundle.pullback f.toMul.hom.hom.left) 0

theorem endomorphismHilbertDifference_zero (D : EndomorphismNumericalPresentation A) :
    endomorphismHilbertDifference A D 0 = 0 := by
  let : Field Γ(Spec (CommRingCat.of K), ⊤) := Quotients.FiniteDescent.FieldPoint.Construction.FieldPointPrime.sectionsField K
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have hc := congrArg Additive.toMul (PicardQuadratic.Construction.algebraicEndLineBundleClass_zero A D.bundle)
  obtain ⟨e⟩ := Quotient.exact hc
  exact EffectiveHilbertDifference.Construction.lineBundleHilbertDifference_eq_zero_of_trivial
    (Affine.ProjectiveEmbedding.Construction.projectiveAffineEmbedding A D.projective) _ 0 e

theorem endomorphismHilbertDifference_leadingCoeff_pos [IsAlgClosed K] [IsProper A.hom]
    (D : EndomorphismNumericalPresentation A) (f : Endomorphisms.Construction.AlgebraicEnd A) (hf : f ≠ 0) :
    0 < (endomorphismHilbertDifference A D f).leadingCoeff := by
  let : Field Γ(Spec (CommRingCat.of K), ⊤) := Quotients.FiniteDescent.FieldPoint.Construction.FieldPointPrime.sectionsField K
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  apply EffectiveHilbertDifference.Construction.lineBundleHilbertDifference_leadingCoeff_pos
    (Affine.ProjectiveEmbedding.Construction.projectiveAffineEmbedding A D.projective) _ 0 (D.frames.pullback f.toMul.hom.hom.left)
  intro he
  apply hf
  apply (PicardQuadratic.Construction.algebraicEndLineBundleClass_eq_zero_iff A D.bundle D.ample f).mp
  apply Additive.toMul.injective
  exact Quotient.sound he

theorem endomorphismHilbertDifference_eq_zero_iff [IsAlgClosed K] [IsProper A.hom]
    (D : EndomorphismNumericalPresentation A) (f : Endomorphisms.Construction.AlgebraicEnd A) :
    endomorphismHilbertDifference A D f = 0 ↔ f = 0 := by
  constructor
  · intro h
    by_contra hf
    have hp := endomorphismHilbertDifference_leadingCoeff_pos A D f hf
    rw [h, Polynomial.leadingCoeff_zero] at hp
    exact (lt_irrefl 0) hp
  · rintro rfl
    exact endomorphismHilbertDifference_zero A D

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.HilbertDifference
