import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FlatProjectiveHilbertBounds
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.EmbeddedAmpleSectionDimension
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PolynomialRankSandwich

/-! # Finite Flat Projective Degree -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteFlatProjectiveDegree.Construction

noncomputable section

/-! A rescaled projective Hilbert polynomial determines the actual generic degree of a finite flat map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory _root_.MvPolynomial

local instance finiteFlatProjectiveDegreeMonoidal (X : Scheme.{0}) :
    MonoidalCategory X.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

variable {R : Type} [CommRing R] [IsNoetherianRing R]
    {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem finiteFlat_projective_rank_of_rescaling
    (hfield : IsField Γ(Spec (.of R), ⊤)) {X Z : Scheme} [IsIntegral X] [IsIntegral Z]
    (f : X ⟶ Z) [IsFinite f] [Flat f] [Surjective f]
    (a : Z ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion a] (j : σ)
    (P Q : Polynomial ℚ) (hPne : P ≠ 0) (b : ℕ)
    (hP : ∀ n, b ≤ n →
      (Module.finrank Γ(Spec (.of R), ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
        ((Scheme.Modules.pullback a).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n))) : ℚ) = P.eval (n : ℚ))
    (hQ : ∀ n, b ≤ n →
      (Module.finrank Γ(Spec (.of R), ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
        ((Scheme.Modules.pushforward f).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) ⊗
          (Scheme.Modules.pullback a).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n))) : ℚ) = Q.eval (n : ℚ))
    (s : ℕ) (hs : 0 < s) (he : Q = P.comp (Polynomial.X * Polynomial.C (s : ℚ))) :
    ∃ z : Z, f.finrank z = s ^ P.natDegree := by
  let := hfield.toField
  let z : Z := Classical.choice inferInstance
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show a z ∈ ⨆ i : σ, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i by
      rw [AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top]; trivial)
  have : Nonempty (a ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i) := ⟨⟨z, hi⟩⟩
  obtain ⟨x, hx⟩ := f.surjective z
  have : Nonempty ((f ≫ a) ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i) :=
    ⟨⟨x, by change a (f x) ∈ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i; rw [hx]; exact hi⟩⟩
  have hp (n : ℕ) (hn : b ≤ n) :
      (Module.finrank Γ(Spec (.of R), ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
        ((Scheme.Modules.pullback a).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower i n))) : ℚ) = P.eval (n : ℚ) := by
    let e := (Scheme.Modules.pullback a).mapIso (ProjectiveCoordinateBundleIso.Construction.projectiveTwistCoordinateIso (R := R) j i n)
    have h := ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).mapIso e).toLinearEquiv.finrank_eq
    exact (congrArg (fun k : ℕ => (k : ℚ)) h).symm.trans (hP n hn)
  have hq (n : ℕ) (hn : b ≤ n) :
      (Module.finrank Γ(Spec (.of R), ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
        ((Scheme.Modules.pushforward f).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) ⊗
          (Scheme.Modules.pullback a).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower i n))) : ℚ) = Q.eval (n : ℚ) :=
    (congrArg (fun k : ℕ => (k : ℚ)) (EmbeddedAmpleSectionDimension.Construction.projectiveTwistedSection_finrank_coordinate a
      ((Scheme.Modules.pushforward f).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)) j i n)).symm.trans (hQ n hn)
  obtain ⟨c, t, hlo, hhi⟩ := FlatProjectiveHilbertBounds.Construction.finiteFlatProjective_Hilbert_shift_bounds hfield f a i P Q b hp hq
  let z₀ := ((AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen (R := R) i).preimage a).fromSpec
    (⊥ : PrimeSpectrum Γ(Z, a ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i))
  exact ⟨z₀, PolynomialRankSandwich.Construction.polynomial_rank_eq_power_of_rescaling_and_shift_bounds
    P Q hPne (f.finrank z₀) s hs he c t hlo hhi⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteFlatProjectiveDegree.Construction
