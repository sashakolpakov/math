import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedCodimension

/-! # Closed Dimension -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedDimension

noncomputable section

/-! A nonempty smooth closed subscheme has relative dimension at most
that of its smooth ambient scheme, by the actual conormal exact sequence. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y S : Scheme.{u}} [IsAffine S]
  (f : X ⟶ Y) [IsClosedImmersion f] (π : Y ⟶ S) (N g : ℕ)
  [SmoothOfRelativeDimension N π] [SmoothOfRelativeDimension g (f ≫ π)]

include π in
theorem dimension_le (U : Y.Opens) (hU : IsAffineOpen U)
    [IsNoetherianRing Γ(Y, U)] (x : X) (hx : f x ∈ U) : g ≤ N := by
  let := ClosedSections.algebra π U
  have : Smooth π := SmoothOfRelativeDimension.smooth N π
  have : Smooth (f ≫ π) := SmoothOfRelativeDimension.smooth g (f ≫ π)
  have := ClosedSections.smooth_sections π U hU
  have := ClosedSections.smooth_quotient f π U hU
  let p₀ := hU.primeIdealOf ⟨f x, hx⟩
  have hp₀ : f.ker.ideal ⟨U, hU⟩ ≤ p₀.asIdeal :=
    ClosedNeighborhood.kernel_le_prime f U hU x hx
  let p := (f.ker.ideal ⟨U, hU⟩).primeSpectrumQuotientOrderIsoZeroLocus.symm ⟨p₀, hp₀⟩
  have hr := ConormalRank.quotient_rank (k := Γ(S, ⊤)) (f.ker.ideal ⟨U, hU⟩) p
  rw [RelativeRank.sections_rank π N U hU,
    RelativeRank.quotient_rank f π g U hU] at hr
  omega

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem projective {X : Scheme.{u}} [Nonempty X]
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f] (g : ℕ)
    [SmoothOfRelativeDimension g (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] : g ≤ Fintype.card σ - 1 := by
  let x : X := Classical.choice inferInstance
  have hx : f x ∈ ⨆ i : σ, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i := by
    rw [AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let : SmoothOfRelativeDimension (Fintype.card σ - 1)
      (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) := IntegralComparison.Projective.RelativeDimension.smooth
  let : LocallyOfFiniteType (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) :=
    AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ_locallyOfFiniteType
  let : IsLocallyNoetherian (Proj (homogeneousSubmodule σ R)) :=
    LocallyOfFiniteType.isLocallyNoetherian (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
  let : IsNoetherianRing Γ(Proj (homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) :=
    IsLocallyNoetherian.component_noetherian ⟨_, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩
  exact dimension_le f AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (Fintype.card σ - 1) g
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i) x hi

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedDimension
