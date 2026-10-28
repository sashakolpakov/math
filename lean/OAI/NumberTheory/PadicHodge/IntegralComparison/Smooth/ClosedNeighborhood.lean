import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SpaceSmooth
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Closed Neighborhood -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedNeighborhood

noncomputable section

/-! Every point of a smooth closed subscheme of projective space has an
actual affine coordinate subneighborhood with regular defining equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
  (U : Y.Opens) (hU : IsAffineOpen U) (x : X) (hx : f x ∈ U)

theorem kernel_le_prime :
    f.ker.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf ⟨f x, hx⟩).asIdeal := by
  let q := (hU.preimage f).primeIdealOf ⟨x, hx⟩
  have he : q.comap (f.app U).hom = hU.primeIdealOf ⟨f x, hx⟩ := by
    simpa only [Scheme.Hom.appLE_eq_app] using
      IsAffineOpen.comap_primeIdealOf_appLE U hU (f ⁻¹ᵁ U) (hU.preimage f) le_rfl hx
  rw [f.ker_apply, ← congrArg PrimeSpectrum.asIdeal he]
  intro a ha
  change f.app U a ∈ q.asIdeal
  rw [RingHom.mem_ker.mp ha]
  exact q.asIdeal.zero_mem

variable {S : Scheme.{u}} [IsAffine S] (π : Y ⟶ S) [Smooth π] [Smooth (f ≫ π)]

include hU hx π in
theorem exists_neighborhood [IsNoetherianRing Γ(Y, U)] :
    ∃ (V : Y.Opens) (_hV : IsAffineOpen V), V ≤ U ∧ f x ∈ V ∧
      ∃ rs : List Γ(Y, V), RingHom.ker (f.app V).hom = Ideal.ofList rs ∧
        RingTheory.Sequence.IsRegular Γ(Y, V) rs := by
  obtain ⟨V, hV, hVU, hpV, rs, hI, hreg⟩ :=
    ClosedSections.exists_regular_subopen f π U hU (hU.primeIdealOf ⟨f x, hx⟩)
      (kernel_le_prime f U hU x hx)
  rw [hU.fromSpec_primeIdealOf] at hpV
  exact ⟨V, hV, hVU, hpV, rs, hI, hreg⟩

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem projective_neighborhood {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f]
    [Smooth (f ≫ OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] (x : X) :
    ∃ (i : σ) (V : (Proj (homogeneousSubmodule σ R)).Opens) (_hV : IsAffineOpen V),
      V ≤ OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i ∧ f x ∈ V ∧
        ∃ rs : List Γ(Proj (homogeneousSubmodule σ R), V),
          RingHom.ker (f.app V).hom = Ideal.ofList rs ∧
            RingTheory.Sequence.IsRegular Γ(Proj (homogeneousSubmodule σ R), V) rs := by
  have hx : f x ∈ ⨆ i : σ, OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i := by
    rw [OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let : Smooth (OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) := IntegralComparison.Projective.SpaceSmooth.smooth
  let : LocallyOfFiniteType (OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) :=
    OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ_locallyOfFiniteType
  let : IsLocallyNoetherian (Proj (homogeneousSubmodule σ R)) :=
    LocallyOfFiniteType.isLocallyNoetherian (OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
  let : IsNoetherianRing Γ(Proj (homogeneousSubmodule σ R), OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) :=
    IsLocallyNoetherian.component_noetherian ⟨_, OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩
  obtain ⟨V, hV, hVi, hxV, rs, hI, hreg⟩ :=
    exists_neighborhood f (OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i)
      x hi OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ
  exact ⟨i, V, hV, hVi, hxV, rs, hI, hreg⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedNeighborhood
