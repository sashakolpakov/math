import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.Numerics
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.SectionFiniteness
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalSectionsMono

/-! # Hilbert Monotonicity -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.HilbertMonotonicity

noncomputable section

/-! Actual injections of coherent projective modules give inequalities
of section dimensions and eventual inequalities of their Hilbert polynomials. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u

open OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalSectionsMono

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] {r : ℕ}
  {M N : (Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)).Modules}
  [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent] [N.IsFiniteType]

omit [M.IsQuasicoherent] [M.IsFiniteType] in
theorem projectiveHilbertFunction_le_of_mono (f : M ⟶ N) [Mono f]
    (j : Fin (r + 1)) (n : ℕ) :
    Projective.Numerics.Construction.projectiveHilbertFunction M j n ≤ Projective.Numerics.Construction.projectiveHilbertFunction N j n := by
  let F := (SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := K) j n).functor
  let G := SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor
    (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) (σ := Fin (r + 1)))
  have : (F.obj N).IsQuasicoherent :=
    SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial.moduleTensorCoordinateHyperplanePoleSheafPower_isQuasicoherent N j n
  have : (F.obj N).IsFiniteType :=
    SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial.moduleTensorCoordinateHyperplanePoleSheafPower_isFiniteType N j n
  have : Module.Finite Γ(Spec (CommRingCat.of K), ⊤) (G.obj (F.obj N)) :=
    Projective.SectionFiniteness.Construction.projectiveGlobalSections_finite (F.obj N)
  let : Field Γ(Spec (CommRingCat.of K), ⊤) := Projective.Numerics.Construction.fieldSpec_sections_isField.toField
  let a := (G.map (F.map f)).hom
  have ha : Function.Injective a := SheafCohomology.Projective.GlobalSectionsMono.globalSections_injective_of_mono (F.map f)
  change (Module.finrank Γ(Spec (CommRingCat.of K), ⊤) (G.obj (F.obj M)) : ℚ) ≤
    (Module.finrank Γ(Spec (CommRingCat.of K), ⊤) (G.obj (F.obj N)) : ℚ)
  exact_mod_cast LinearMap.finrank_le_finrank_of_injective ha

theorem projectiveHilbertPolynomial_eventually_le_of_mono (f : M ⟶ N) [Mono f]
    (j : Fin (r + 1)) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      (Projective.Numerics.Construction.projectiveHilbertPolynomial M j).eval (n : ℚ) ≤
        (Projective.Numerics.Construction.projectiveHilbertPolynomial N j).eval (n : ℚ) := by
  obtain ⟨b, hb⟩ := Projective.Numerics.Construction.projectiveHilbertPolynomial_spec M j
  obtain ⟨c, hc⟩ := Projective.Numerics.Construction.projectiveHilbertPolynomial_spec N j
  refine ⟨max b c, fun n hn => ?_⟩
  rw [← hb n ((le_max_left _ _).trans hn), ← hc n ((le_max_right _ _).trans hn)]
  exact projectiveHilbertFunction_le_of_mono f j n

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.HilbertMonotonicity
