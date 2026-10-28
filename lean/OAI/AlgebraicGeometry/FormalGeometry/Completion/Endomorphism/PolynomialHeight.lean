import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.HilbertDifference
import OAI.AlgebraicGeometry.FormalGeometry.Completion.NumericalDegreeProperties
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialQuadratic

/-! # Polynomial Height -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PolynomialHeight

noncomputable section

/-! The actual endomorphism Hilbert invariant satisfies the polynomial
height identities required for descent through successive zero subgroups. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [GeometricallyIntegral A.hom] [IsProper A.hom] [Smooth A.hom]

theorem endomorphismHilbertDifference_coeff_parallelogram
    (D : HilbertDifference.Construction.EndomorphismNumericalPresentation A) (d : ℕ) (f g : Endomorphisms.Construction.AlgebraicEnd A)
    (hf : (HilbertDifference.Construction.endomorphismHilbertDifference A D f).natDegree ≤ d)
    (hg : (HilbertDifference.Construction.endomorphismHilbertDifference A D g).natDegree ≤ d)
    (hfg : (HilbertDifference.Construction.endomorphismHilbertDifference A D (f + g)).natDegree ≤ d) :
    (HilbertDifference.Construction.endomorphismHilbertDifference A D (f + g)).coeff d +
      (HilbertDifference.Construction.endomorphismHilbertDifference A D (f - g)).coeff d =
        2 * ((HilbertDifference.Construction.endomorphismHilbertDifference A D f).coeff d + (HilbertDifference.Construction.endomorphismHilbertDifference A D g).coeff d) := by
  let : Field Γ(Spec (CommRingCat.of K), ⊤) := Quotients.FiniteDescent.FieldPoint.Construction.FieldPointPrime.sectionsField K
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : Infinite Γ(Spec (CommRingCat.of K), ⊤) :=
    Infinite.of_injective (Scheme.ΓSpecIso (CommRingCat.of K)).inv
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1
  let e := Affine.ProjectiveEmbedding.Construction.projectiveAffineEmbedding A D.projective
  let B (t : Endomorphisms.Construction.AlgebraicEnd A) := D.bundle.pullback t.toMul.hom.hom.left
  have hB (t : Endomorphisms.Construction.AlgebraicEnd A) : Frame.SectionDetection.Construction.HasFrameSections (B t).sheaf := D.frames.pullback t.toMul.hom.hom.left
  have h₁ := LineBundleHilbertCoefficients.Construction.lineBundleHilbertCoefficient_tensor_generated_left e (B (f + g)) (B (f - g))
    (hB (f + g)) 0 d hfg
  have h₂ := LineBundleHilbertCoefficients.Construction.lineBundleHilbertCoefficient_tensor_generated_left e (B f) ((B f).tensor ((B g).tensor (B g)))
    (hB f) 0 d hf
  have h₃ := LineBundleHilbertCoefficients.Construction.lineBundleHilbertCoefficient_tensor_generated_left e (B f) ((B g).tensor (B g))
    (hB f) 0 d hf
  have h₄ := LineBundleHilbertCoefficients.Construction.lineBundleHilbertCoefficient_tensor_generated_left e (B g) (B g) (hB g) 0 d hg
  have hi := PicardQuadratic.Construction.algebraicEndLineBundleClass_parallelogram A D.bundle D.symmetric f g
  rw [two_nsmul, two_nsmul] at hi
  have hm := congrArg Additive.toMul hi
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (B (f + g)) * AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (B (f - g)) =
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (B f) * AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (B f)) *
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (B g) * AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (B g)) at hm
  rw [mul_assoc] at hm
  have he : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((B (f + g)).tensor (B (f - g))) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((B f).tensor ((B f).tensor ((B g).tensor (B g)))) := hm
  obtain ⟨iso⟩ := Quotient.exact he
  have hc := LineBundleHilbertCoefficients.Construction.lineBundleHilbertCoefficient_iso e _ _ iso 0 d
  change LineBundleHilbertCoefficients.Construction.lineBundleHilbertCoefficient e (B (f + g)) 0 d + LineBundleHilbertCoefficients.Construction.lineBundleHilbertCoefficient e (B (f - g)) 0 d =
    2 * (LineBundleHilbertCoefficients.Construction.lineBundleHilbertCoefficient e (B f) 0 d + LineBundleHilbertCoefficients.Construction.lineBundleHilbertCoefficient e (B g) 0 d)
  linarith

omit [IsAlgClosed K] [IsProper A.hom] [Smooth A.hom] [IsCommMonObj A] in
theorem endomorphismHilbertDifference_eventually_integer
    (D : HilbertDifference.Construction.EndomorphismNumericalPresentation A) (f : Endomorphisms.Construction.AlgebraicEnd A) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → ∃ z : ℤ, (HilbertDifference.Construction.endomorphismHilbertDifference A D f).eval (n : ℚ) = z := by
  let : Field Γ(Spec (CommRingCat.of K), ⊤) := Quotients.FiniteDescent.FieldPoint.Construction.FieldPointPrime.sectionsField K
  exact NumericalDegreeProperties.Construction.lineBundleHilbertDifference_eventually_integer (Affine.ProjectiveEmbedding.Construction.projectiveAffineEmbedding A D.projective)
    (D.bundle.pullback f.toMul.hom.hom.left) 0

def endomorphismPolynomialQuadraticHeight (D : HilbertDifference.Construction.EndomorphismNumericalPresentation A) :
    PolynomialQuadratic.Construction.PolynomialQuadraticHeight (Endomorphisms.Construction.AlgebraicEnd A) where
  value := HilbertDifference.Construction.endomorphismHilbertDifference A D
  zero := HilbertDifference.Construction.endomorphismHilbertDifference_zero A D
  detectsZero f hf := (HilbertDifference.Construction.endomorphismHilbertDifference_eq_zero_iff A D f).mp hf
  positive := HilbertDifference.Construction.endomorphismHilbertDifference_leadingCoeff_pos A D
  integer_values := endomorphismHilbertDifference_eventually_integer A D
  coeff_parallelogram := endomorphismHilbertDifference_coeff_parallelogram A D

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PolynomialHeight
