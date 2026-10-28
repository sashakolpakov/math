import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.RegularSubopenLength
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedNeighborhood
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.RelativeRank
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.RelativeDimension

/-! # Closed Codimension -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedCodimension

noncomputable section

/-! Smooth closed immersions admit regular equations of the true
relative codimension on actual affine coordinate neighborhoods. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y S : Scheme.{u}} [IsAffine S]
  (f : X ⟶ Y) [IsClosedImmersion f] (π : Y ⟶ S) (N g : ℕ)
  [SmoothOfRelativeDimension N π] [SmoothOfRelativeDimension g (f ≫ π)]

include π in
theorem exists_neighborhood (U : Y.Opens) (hU : IsAffineOpen U)
    [IsNoetherianRing Γ(Y, U)] (x : X) (hx : f x ∈ U) :
    ∃ (V : Y.Opens) (_hV : IsAffineOpen V), V ≤ U ∧ f x ∈ V ∧
      ∃ rs : List Γ(Y, V), RingHom.ker (f.app V).hom = Ideal.ofList rs ∧
        RingTheory.Sequence.IsRegular Γ(Y, V) rs ∧ rs.length = N - g := by
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
  obtain ⟨V, hV, hVU, hxV, rs, hI, hreg, hlen⟩ :=
    RegularSubopenLength.exists_regular_subopen (k := Γ(S, ⊤)) f.ker U hU p
  rw [hp] at hxV
  rw [hU.fromSpec_primeIdealOf] at hxV
  rw [RelativeRank.sections_rank π N U hU,
    RelativeRank.quotient_rank f π g U hU] at hlen
  exact ⟨V, hV, hVU, hxV, rs, (f.ker_apply ⟨V, hV⟩).symm.trans hI, hreg, hlen⟩

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem projective_neighborhood {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f] (g : ℕ)
    [SmoothOfRelativeDimension g (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] (x : X) :
    ∃ (i : σ) (V : (Proj (homogeneousSubmodule σ R)).Opens) (_hV : IsAffineOpen V),
      V ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i ∧ f x ∈ V ∧
        ∃ rs : List Γ(Proj (homogeneousSubmodule σ R), V),
          RingHom.ker (f.app V).hom = Ideal.ofList rs ∧
            RingTheory.Sequence.IsRegular Γ(Proj (homogeneousSubmodule σ R), V) rs ∧
              rs.length = Fintype.card σ - 1 - g := by
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
  obtain ⟨V, hV, hVi, hxV, rs, hI, hreg, hlen⟩ :=
    exists_neighborhood f AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (Fintype.card σ - 1) g
      (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i) x hi
  exact ⟨i, V, hV, hVi, hxV, rs, hI, hreg, hlen⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedCodimension
