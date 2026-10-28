import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FlatProjectiveRankBounds
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CompositePushforwardProjectiveSections

/-! # Flat Projective Hilbert Bounds -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FlatProjectiveHilbertBounds.Construction

noncomputable section

/-! The actual projective Hilbert polynomials satisfy the shifted inequalities of a finite flat map's rank. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory _root_.MvPolynomial

universe u

local instance finiteFlatProjectiveHilbertBoundsMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
    {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem finiteFlatProjective_Hilbert_shift_bounds
    (hfield : IsField Γ(Spec (.of R), ⊤)) {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    (f : X ⟶ Z) [IsFinite f] [Flat f]
    (a : Z ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion a] (j : σ)
    [Nonempty (a ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)] [Nonempty ((f ≫ a) ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)]
    (P Q : Polynomial ℚ) (b : ℕ)
    (hP : ∀ n, b ≤ n →
      (Module.finrank Γ(Spec (.of R), ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
        ((Scheme.Modules.pullback a).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n))) : ℚ) = P.eval (n : ℚ))
    (hQ : ∀ n, b ≤ n →
      (Module.finrank Γ(Spec (.of R), ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
        ((Scheme.Modules.pushforward f).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) ⊗
          (Scheme.Modules.pullback a).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n))) : ℚ) = Q.eval (n : ℚ)) :
    let D := f.finrank (((AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen (R := R) j).preimage a).fromSpec
      (⊥ : PrimeSpectrum Γ(Z, a ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)))
    ∃ c s : ℕ,
      (∀ n, c ≤ n → (D : ℚ) * P.eval (n : ℚ) ≤ Q.eval ((n : ℚ) + s)) ∧
      (∀ n, c ≤ n → Q.eval (n : ℚ) ≤ (D : ℚ) * P.eval ((n : ℚ) + s)) := by
  let := hfield.toField
  let := BaseOpenSections.Construction.baseOpenSectionsAlgebra (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (a ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  let D := f.finrank (((AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen (R := R) j).preimage a).fromSpec
    (⊥ : PrimeSpectrum Γ(Z, a ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)))
  let N := (Scheme.Modules.pushforward (f ≫ a)).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)
  obtain ⟨b₀, s, hlo, hhi⟩ := FlatProjectiveRankBounds.Construction.finiteFlatProjective_sections_filtered_rank_bounds hfield f a j
  obtain ⟨b₁, hb₁⟩ := ProjectiveFilteredSections.Construction.closedProjective_sections_filtered_finrank hfield a j
  let c := max b (max b₀ b₁)
  have hcP (n : ℕ) (hn : c ≤ n) := (le_max_left b (max b₀ b₁)).trans hn
  have hc₀ (n : ℕ) (hn : c ≤ n) := (le_max_left b₀ b₁).trans ((le_max_right b (max b₀ b₁)).trans hn)
  have hc₁ (n : ℕ) (hn : c ≤ n) := (le_max_right b₀ b₁).trans ((le_max_right b (max b₀ b₁)).trans hn)
  have hp (n : ℕ) (hn : c ≤ n) :
      (Module.finrank Γ(Spec (.of R), ⊤)
        (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := Γ(Spec (.of R), ⊤)) (ProjectiveFilteredSections.Construction.closedProjectiveChartCoordinates a j) n) : ℚ) =
      P.eval (n : ℚ) :=
    (congrArg (fun k : ℕ => (k : ℚ)) (hb₁ n (hc₁ n hn))).symm.trans (hP n (hcP n hn))
  have hq (n : ℕ) (hn : c ≤ n) :
      (Module.finrank Γ(Spec (.of R), ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ).obj
        (N ⊗ AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n)) : ℚ) = Q.eval (n : ℚ) :=
    (congrArg (fun k : ℕ => (k : ℚ))
      (CompositePushforwardProjectiveSections.Construction.compositePushforwardProjectiveSectionsEquiv f a j n).finrank_eq).symm.trans (hQ n (hcP n hn))
  refine ⟨c, s, ?_, ?_⟩
  · intro n hn
    have h : (D : ℚ) * (Module.finrank Γ(Spec (.of R), ⊤)
        (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := Γ(Spec (.of R), ⊤)) (ProjectiveFilteredSections.Construction.closedProjectiveChartCoordinates a j) n) : ℚ) ≤
        (Module.finrank Γ(Spec (.of R), ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ).obj
          (N ⊗ AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j (n + s))) : ℚ) := by
      exact_mod_cast hlo n (hc₀ n hn)
    rw [hp n hn, hq (n + s) (hn.trans (Nat.le_add_right n s))] at h
    simpa only [Nat.cast_add] using h
  · intro n hn
    have h : (Module.finrank Γ(Spec (.of R), ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ).obj
        (N ⊗ AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n)) : ℚ) ≤
        (D : ℚ) * (Module.finrank Γ(Spec (.of R), ⊤)
          (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := Γ(Spec (.of R), ⊤))
            (ProjectiveFilteredSections.Construction.closedProjectiveChartCoordinates a j) (n + s)) : ℚ) := by
      exact_mod_cast hhi n (hc₀ n hn)
    rw [hq n hn, hp (n + s) (hn.trans (Nat.le_add_right n s))] at h
    simpa only [Nat.cast_add] using h

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FlatProjectiveHilbertBounds.Construction
