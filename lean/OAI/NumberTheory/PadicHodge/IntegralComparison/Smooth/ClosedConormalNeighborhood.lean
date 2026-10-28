import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ConormalSubopen
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedCodimension

/-! # Closed Conormal Neighborhood -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedConormalNeighborhood

noncomputable section

/-! Smooth closed immersions have genuine affine neighborhoods with
regular equations, their matching conormal basis, and the geometric
codimension. These data are consequences of smoothness. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X Y S : Scheme.{u}} [IsAffine S]
  (f : X ⟶ Y) [IsClosedImmersion f] (π : Y ⟶ S) (N g : ℕ)
  [SmoothOfRelativeDimension N π] [SmoothOfRelativeDimension g (f ≫ π)]

include π in
theorem exists_neighborhood (U : Y.Opens) (hU : IsAffineOpen U)
    [IsNoetherianRing Γ(Y, U)] (x : X) (hx : f x ∈ U) :
    ∃ (V : Y.Opens) (hV : IsAffineOpen V), V ≤ U ∧ f x ∈ V ∧
      ∃ (c : ℕ) (s : Fin c → Γ(Y, V))
        (hs : Koszul.OrientedTopCohomology.ideal Γ(Y, V) s = f.ker.ideal ⟨V, hV⟩),
        RingTheory.Sequence.IsRegular Γ(Y, V) (List.ofFn s) ∧
        ∃ b : Module.Basis (Fin c) (Γ(Y, V) ⧸ f.ker.ideal ⟨V, hV⟩) (f.ker.ideal ⟨V, hV⟩).Cotangent,
          (∀ j, b j = (f.ker.ideal ⟨V, hV⟩).toCotangent
            (ConormalKoszulPurity.conormalVectors Γ(Y, V) (f.ker.ideal ⟨V, hV⟩) s hs j)) ∧
          c = N - g := by
  let := ClosedSections.algebra π U
  have : Smooth π := SmoothOfRelativeDimension.smooth N π
  have : Smooth (f ≫ π) := SmoothOfRelativeDimension.smooth g (f ≫ π)
  have := ClosedSections.smooth_sections π U hU
  have := ClosedSections.smooth_quotient f π U hU
  let p₀ := hU.primeIdealOf ⟨f x, hx⟩
  have hp₀ : f.ker.ideal ⟨U, hU⟩ ≤ p₀.asIdeal :=
    ClosedNeighborhood.kernel_le_prime f U hU x hx
  let p := (f.ker.ideal ⟨U, hU⟩).primeSpectrumQuotientOrderIsoZeroLocus.symm ⟨p₀, hp₀⟩
  have hp : p.comap (Ideal.Quotient.mk (f.ker.ideal ⟨U, hU⟩)) = p₀ :=
    congrArg Subtype.val
      ((f.ker.ideal ⟨U, hU⟩).primeSpectrumQuotientOrderIsoZeroLocus.apply_symm_apply ⟨p₀, hp₀⟩)
  obtain ⟨V, hV, hVU, hxV, c, s, hs, hr, b, hb, hlen⟩ :=
    ConormalSubopen.exists_subopen (k := Γ(S, ⊤)) f.ker U hU p
  rw [hp, hU.fromSpec_primeIdealOf] at hxV
  rw [RelativeRank.sections_rank π N U hU,
    RelativeRank.quotient_rank f π g U hU] at hlen
  exact ⟨V, hV, hVU, hxV, c, s, hs, hr, b, hb, hlen⟩

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem projective_neighborhood {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f] (g : ℕ)
    [SmoothOfRelativeDimension g (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] (x : X) :
    ∃ (i : σ) (V : (Proj (homogeneousSubmodule σ R)).Opens) (hV : IsAffineOpen V),
      V ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i ∧ f x ∈ V ∧
        ∃ (c : ℕ) (s : Fin c → Γ(Proj (homogeneousSubmodule σ R), V))
          (hs : Koszul.OrientedTopCohomology.ideal Γ(Proj (homogeneousSubmodule σ R), V) s =
            f.ker.ideal ⟨V, hV⟩),
          RingTheory.Sequence.IsRegular Γ(Proj (homogeneousSubmodule σ R), V) (List.ofFn s) ∧
          ∃ b : Module.Basis (Fin c)
              (Γ(Proj (homogeneousSubmodule σ R), V) ⧸ f.ker.ideal ⟨V, hV⟩)
              (f.ker.ideal ⟨V, hV⟩).Cotangent,
            (∀ j, b j = (f.ker.ideal ⟨V, hV⟩).toCotangent
              (ConormalKoszulPurity.conormalVectors
                Γ(Proj (homogeneousSubmodule σ R), V) (f.ker.ideal ⟨V, hV⟩) s hs j)) ∧
            c = Fintype.card σ - 1 - g := by
  have hx : f x ∈ ⨆ i : σ, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i := by
    rw [AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let : SmoothOfRelativeDimension (Fintype.card σ - 1)
      (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) := IntegralComparison.Projective.RelativeDimension.smooth
  let : LocallyOfFiniteType (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ_locallyOfFiniteType
  let : IsLocallyNoetherian (Proj (homogeneousSubmodule σ R)) :=
    LocallyOfFiniteType.isLocallyNoetherian (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
  let : IsNoetherianRing Γ(Proj (homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) :=
    IsLocallyNoetherian.component_noetherian ⟨_, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩
  obtain ⟨V, hV, hVi, hxV, c, s, hs, hr, b, hb, hc⟩ :=
    exists_neighborhood f AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (Fintype.card σ - 1) g
      (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i) x hi
  exact ⟨i, V, hV, hVi, hxV, c, s, hs, hr, b, hb, hc⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedConormalNeighborhood
