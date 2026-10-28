import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.Numerics
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.SectionFiniteness
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialPositivity
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedSectionsDetectZero

/-! # Hilbert Positivity -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.HilbertPositivity

noncomputable section

/-! The canonical Hilbert polynomial of a nonzero coherent projective module
is nonzero and has positive leading coefficient over every field. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory

namespace Construction

universe u

attribute [local instance] MvPolynomial.gradedAlgebra SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory

variable {K : Type u} [Field K] {r : ℕ}
  (M : (Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType] (j : Fin (r + 1))

theorem projectiveHilbertPolynomial_eq_zero_of_isZero (h : IsZero M) :
    Projective.Numerics.Construction.projectiveHilbertPolynomial M j = 0 := by
  apply EventualPolynomial.Construction.eventualPolynomialValue_eq _ _ 0
  intro n _
  let F := (SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := K) j n).functor
  let G := SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor
    (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) (σ := Fin (r + 1)))
  have : Subsingleton (G.obj (F.obj M)) :=
    ModuleCat.subsingleton_of_isZero ((F ⋙ G).map_isZero h)
  let : Field Γ(Spec (CommRingCat.of K), ⊤) := Projective.Numerics.Construction.fieldSpec_sections_isField.toField
  have hz := Module.finrank_eq_zero_of_subsingleton Γ(Spec (CommRingCat.of K), ⊤)
    (G.obj (F.obj M))
  rw [Polynomial.eval_zero]
  change (Module.finrank Γ(Spec (CommRingCat.of K), ⊤) (G.obj (F.obj M)) : ℚ) = 0
  exact_mod_cast hz

theorem projectiveHilbertPolynomial_isZero_of_eq_zero
    (h : Projective.Numerics.Construction.projectiveHilbertPolynomial M j = 0) : IsZero M := by
  obtain ⟨b, hb⟩ := Projective.Numerics.Construction.projectiveHilbertPolynomial_spec M j
  apply SheafCohomology.Projective.TwistedSectionsDetectZero.MvPolynomial.finiteType_isZero_of_eventually_twistedSections_subsingleton M j b
  intro n hn
  let N := M ⊗ SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) j n
  have : N.IsQuasicoherent :=
    SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial.moduleTensorCoordinateHyperplanePoleSheafPower_isQuasicoherent M j n
  have : N.IsFiniteType :=
    SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial.moduleTensorCoordinateHyperplanePoleSheafPower_isFiniteType M j n
  let S := (SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor
    (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) (σ := Fin (r + 1)))).obj N
  have : Module.Finite Γ(Spec (CommRingCat.of K), ⊤) S := Projective.SectionFiniteness.Construction.projectiveGlobalSections_finite N
  let : Field Γ(Spec (CommRingCat.of K), ⊤) := Projective.Numerics.Construction.fieldSpec_sections_isField.toField
  have hdim : Module.finrank Γ(Spec (CommRingCat.of K), ⊤) S = 0 := by
    have hv := hb n hn
    rw [h, Polynomial.eval_zero] at hv
    change (Module.finrank Γ(Spec (CommRingCat.of K), ⊤) S : ℚ) = 0 at hv
    exact_mod_cast hv
  exact (Module.finrank_eq_zero_iff_of_free Γ(Spec (CommRingCat.of K), ⊤) S).mp hdim

theorem projectiveHilbertPolynomial_eq_zero_iff :
    Projective.Numerics.Construction.projectiveHilbertPolynomial M j = 0 ↔ IsZero M :=
  ⟨projectiveHilbertPolynomial_isZero_of_eq_zero M j,
    projectiveHilbertPolynomial_eq_zero_of_isZero M j⟩

theorem projectiveHilbertPolynomial_ne_zero (h : ¬ IsZero M) :
    Projective.Numerics.Construction.projectiveHilbertPolynomial M j ≠ 0 :=
  fun hz => h (projectiveHilbertPolynomial_isZero_of_eq_zero M j hz)

theorem projectiveHilbertPolynomial_leadingCoeff_pos (h : ¬ IsZero M) :
    0 < (Projective.Numerics.Construction.projectiveHilbertPolynomial M j).leadingCoeff := by
  obtain ⟨b, hb⟩ := Projective.Numerics.Construction.projectiveHilbertPolynomial_spec M j
  apply PolynomialPositivity.Construction.polynomial_leadingCoeff_pos_of_eventual_nat_nonneg _
    (projectiveHilbertPolynomial_ne_zero M j h) b
  intro n hn
  rw [← hb n hn]
  exact Nat.cast_nonneg _

theorem projectiveHilbertFunction_eventually_pos (h : ¬ IsZero M) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → 0 < Projective.Numerics.Construction.projectiveHilbertFunction M j n := by
  obtain ⟨b, hb⟩ := Projective.Numerics.Construction.projectiveHilbertPolynomial_spec M j
  obtain ⟨c, hc⟩ := PolynomialPositivity.Construction.polynomial_eventually_nat_pos_of_leadingCoeff_pos _
    (projectiveHilbertPolynomial_leadingCoeff_pos M j h)
  refine ⟨max b c, fun n hn => ?_⟩
  rw [hb n ((le_max_left _ _).trans hn)]
  exact hc n ((le_max_right _ _).trans hn)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.HilbertPositivity
