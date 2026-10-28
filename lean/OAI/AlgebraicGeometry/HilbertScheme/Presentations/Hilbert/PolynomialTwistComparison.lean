import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.ProjectiveHilbertPolynomial
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.IntrinsicCoordinateIdeal

/-! # Polynomial Twist Comparison -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.PolynomialTwistComparison

noncomputable section

/-! Closed projective embeddings with isomorphic pullbacks of every
native twist have exactly the same homogeneous Hilbert-polynomial predicate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

theorem hilbertPolynomial_iff_of_twist_pullback_isos {K : Type u} [Field K]
    {X : Scheme.{u}} {n : ℕ} (f g : X ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading K n))
    [IsClosedImmersion f] [IsClosedImmersion g]
    (π : X ⟶ Spec (.of K)) (hf : f ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = π) (hg : g ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = π)
    (i : Fin (n + 1))
    (h : ∀ m : ℕ, Nonempty ((Scheme.Modules.pullback f).obj (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) i m) ≅
      (Scheme.Modules.pullback g).obj (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) i m))) (P : Polynomial ℚ) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf f.ker).toIdeal P ↔
      Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf g.ker).toIdeal P := by
  let j : Bool → (X ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading K n)) := fun b => cond b f g
  have hj : ∀ b, IsClosedImmersion (j b) := by
    intro b
    cases b
    · exact inferInstanceAs (IsClosedImmersion g)
    · exact inferInstanceAs (IsClosedImmersion f)
  have hπ : ∀ b, j b ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = π := by
    intro b
    cases b
    · exact hg
    · exact hf
  have hL : ∀ b m, Nonempty ((Scheme.Modules.pullback (j b)).obj (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) i m) ≅
      (Scheme.Modules.pullback g).obj (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) i m)) := by
    intro b m
    cases b
    · exact ⟨Iso.refl _⟩
    · exact h m
  have hfield : IsField Γ(Spec (.of K), ⊤) :=
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField K)
  obtain ⟨Q, hQ⟩ := PELModuli.IntegralModel.Fixed.ProjectiveHilbertPolynomial.PolarizationEmbedding.exists_fixed_nativeHilbertPolynomial hfield j π hπ i
    (fun m => (Scheme.Modules.pullback g).obj (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) i m)) hL
  have hQf := (PELModuli.IntegralModel.Presentations.IntrinsicCoordinateIdeal.PolarizationEmbedding.native_hasHilbertPolynomial_iff_e34 f Q).mp (hQ true)
  have hQg := (PELModuli.IntegralModel.Presentations.IntrinsicCoordinateIdeal.PolarizationEmbedding.native_hasHilbertPolynomial_iff_e34 g Q).mp (hQ false)
  constructor
  · intro hP
    exact (Hilbert.Polynomial.GradedHilbert.hilbertPolynomial_unique hP hQf).symm ▸ hQg
  · intro hP
    exact (Hilbert.Polynomial.GradedHilbert.hilbertPolynomial_unique hP hQg).symm ▸ hQf

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.PolynomialTwistComparison
