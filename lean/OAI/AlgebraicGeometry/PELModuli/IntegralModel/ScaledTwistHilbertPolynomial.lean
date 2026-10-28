import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SourcePowerHilbertPolynomial

/-! # Scaled Twist Hilbert Polynomial -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ScaledTwistHilbertPolynomial

noncomputable section

/-! A fixed scaling of the actual hyperplane twists scales the Hilbert
polynomial variable by the same amount. The proof compares native section
dimensions for the two closed embeddings of the same scheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace PolarizationEmbedding
attribute [local instance] MvPolynomial.gradedAlgebra

theorem e34HilbertPolynomial_of_scaled_twists
    {k : Type} [Field k] {X : Scheme.{0}} {n m : ℕ}
    (f : X ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading k n)) (g : X ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading k m))
    [IsClosedImmersion f] [IsClosedImmersion g]
    (hbase : g ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := k) =
      f ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := k))
    (c : ℕ) (hc : 0 < c)
    (hL : ∀ d : ℕ, Nonempty
      ((Scheme.Modules.pullback g).obj (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := k) 0 d) ≅
        (Scheme.Modules.pullback f).obj
          (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := k) 0 (c * d))))
    (P : Polynomial ℚ) (hP : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf f.ker).toIdeal P) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf g.ker).toIdeal
      (P.comp (Polynomial.C (c : ℚ) * Polynomial.X)) := by
  obtain ⟨b, hb⟩ := (Presentations.IntrinsicCoordinateIdeal.PolarizationEmbedding.native_hasHilbertPolynomial_iff_e34 f P).mpr hP
  obtain ⟨a, ha⟩ := Projective.HilbertSections.PolarizationEmbedding.eventually_nativeHilbertFunction_eq_sections f 0
  obtain ⟨e, he⟩ := Projective.HilbertSections.PolarizationEmbedding.eventually_nativeHilbertFunction_eq_sections g 0
  apply (Presentations.IntrinsicCoordinateIdeal.PolarizationEmbedding.native_hasHilbertPolynomial_iff_e34 g _).mp
  refine ⟨max e (max a b), fun d hd => ?_⟩
  have hed : e ≤ d := (le_max_left _ _).trans hd
  have had : a ≤ c * d := (le_max_left a b).trans
    (((le_max_right e (max a b)).trans hd).trans (Nat.le_mul_of_pos_left d hc))
  have hbd : b ≤ c * d := (le_max_right a b).trans
    (((le_max_right e (max a b)).trans hd).trans (Nat.le_mul_of_pos_left d hc))
  have hdim := (Fixed.ProjectiveHilbertPolynomial.PolarizationEmbedding.nativeTwistSectionsFixedEquiv g
    (f ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := k)) hbase 0 d _ (Classical.choice (hL d))).finrank_eq
  have hfun : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertFunction (IntrinsicCoordinateIdeal.PolarizationEmbedding.nativeProjectiveCoordinateIdeal g).toIdeal d =
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertFunction (IntrinsicCoordinateIdeal.PolarizationEmbedding.nativeProjectiveCoordinateIdeal f).toIdeal (c * d) :=
    (he d hed).trans (hdim.trans (ha (c * d) had).symm)
  rw [hfun, hb (c * d) hbd]
  simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Nat.cast_mul]

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ScaledTwistHilbertPolynomial
