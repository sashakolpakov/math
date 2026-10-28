import OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentCechPolynomialAction

/-! # Laurent Top Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentTopCoordinates

noncomputable section

/-! The existing top-cohomology coordinates evaluate a cocycle on the
actual full projective intersection and take its Laurent coefficients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentPolynomialAction OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentCechPolynomialAction

universe u

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

def topIndex (n : ℕ) (hn : Fintype.card σ = n + 1) :
    AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n :=
  AlgebraicGeometry.SheafCohomology.Projective.OrderedCechTopSupport.orderedCechTopIndex n (by simpa using hn)

theorem topIndex_allowed (d : ℤ) (n : ℕ) (hn : Fintype.card σ = n + 1)
    (e : AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d) :
    e.IsAllowedOn (fun k => ((topIndex.{u} (σ := σ) n hn).1 k).down) := by
  intro i _
  obtain ⟨k, hk⟩ := AlgebraicGeometry.SheafCohomology.Projective.OrderedCechTopSupport.orderedCechTopIndex_surjective n
    (show Fintype.card (ULift.{u} σ) = n + 1 by simpa using hn)
    (topIndex.{u} n hn) (ULift.up i)
  exact ⟨k, congrArg (fun x : ULift.{u} σ => x.down) hk⟩

def topAmbient (d : ℤ) (n : ℕ) (hn : Fintype.card σ = n + 1) :
    AlgebraicGeometry.SheafCohomology.Projective.LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n →ₗ[
      Γ(Spec (CommRingCat.of R), ⊤)]
        AddMonoidAlgebra Γ(Spec (CommRingCat.of R), ⊤) (σ →₀ ℤ) :=
  (LaurentPolynomialAction.ambient Γ(Spec (CommRingCat.of R), ⊤) d
    (fun k => ((topIndex.{u} (σ := σ) n hn).1 k).down)).comp
      (Pi.π (LaurentCechPolynomialAction.Factor (R := R) d) (topIndex.{u} n hn)).hom

theorem topAmbient_coefficient (d : ℤ) (n : ℕ) (hn : Fintype.card σ = n + 1)
    (x : AlgebraicGeometry.SheafCohomology.Projective.LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n)
    (e : AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d) :
    (topAmbient (R := R) d n hn x).coeff e.val =
      ((Pi.π (LaurentCechPolynomialAction.Factor (R := R) d) (topIndex.{u} n hn)).hom x).coeff
        ⟨e, topIndex_allowed d n hn e⟩ := by
  have hinj : Function.Injective (fun f : LaurentPolynomialAction.Allowed d
      (fun k => ((topIndex.{u} (σ := σ) n hn).1 k).down) => f.val.val) := by
    intro e f h
    exact Subtype.ext (Subtype.ext h)
  exact Finsupp.mapDomain_apply_of_injective hinj _ ⟨e, topIndex_allowed d n hn e⟩

theorem fullNegativeTopEquiv_apply (d : ℤ) (n : ℕ) (hn : Fintype.card σ = n + 1)
    (s : AlgebraicGeometry.SheafCohomology.Projective.LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCochain.{u, u} (R := R) (σ := σ) d n)
    (e : {e : AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
      e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))}) :
    AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentTop.MvPolynomial.coordinateFullNegativeCochainTopEquiv (R := R) d n hn s e =
      (s e).val (topIndex.{u} n hn) := by
  simp only [AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentTop.MvPolynomial.coordinateFullNegativeCochainTopEquiv, LinearEquiv.piCongrRight_apply,
    LinearEquiv.trans_apply, AlgebraicGeometry.SheafCohomology.Projective.OrderedCechTopSupport.orderedCechFullSupportTopEquiv]
  rfl

theorem projection_top (d : ℤ) (n : ℕ) (hn : Fintype.card σ = n + 1)
    (x : AlgebraicGeometry.SheafCohomology.Projective.LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n)
    (e : {e : AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
      e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))}) :
    AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentTop.MvPolynomial.coordinateFullNegativeCochainTopEquiv (R := R) d n hn
        (AlgebraicGeometry.SheafCohomology.Projective.LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection (R := R) d n x) e =
      (topAmbient (R := R) d n hn x).coeff e.val.val := by
  rw [fullNegativeTopEquiv_apply, AlgebraicGeometry.SheafCohomology.Projective.LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection_apply,
    AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent_apply_of_allowed d e.val (topIndex.{u} n hn)
      (topIndex_allowed d n hn e.val), topAmbient_coefficient]

theorem positiveEquiv_projection (j : σ) (d : ℤ) (n : ℕ)
    (y : (AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).homology (n + 1)) :
    (AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentHomology.MvPolynomial.coordinateHomogeneousLaurentPositiveHomologyEquivFullNegativeCycles (R := R) j d n y).val =
      (AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentHomology.MvPolynomial.coordinateFullNegativeHomologyProjection (R := R) j d n).hom y := by
  obtain ⟨s, hs⟩ :=
    (AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentHomology.MvPolynomial.coordinateHomogeneousLaurentPositiveHomologyEquivFullNegativeCycles (R := R) j d n).symm.surjective y
  subst y
  rw [LinearEquiv.apply_symm_apply]
  exact (ConcreteCategory.congr_hom
    (AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentHomology.MvPolynomial.coordinateFullNegativeCyclesToHomology_projection (R := R) j d n) s).symm

theorem homology_coordinates (j : σ) (d : ℤ) (n : ℕ) (hn : Fintype.card σ = n + 2)
    (z : (AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).cycles (n + 1))
    (e : {e : AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
      e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))}) :
    AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentTop.MvPolynomial.coordinateHomogeneousLaurentTopHomologyEquivCoefficients (R := R) j d n hn
        ((AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).homologyπ (n + 1) z) e =
      (topAmbient (R := R) d (n + 1) hn
        ((AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).iCycles (n + 1) z)).coeff
          e.val.val := by
  change AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentTop.MvPolynomial.coordinateFullNegativeCochainTopEquiv (R := R) d (n + 1) hn
    (AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentHomology.MvPolynomial.coordinateHomogeneousLaurentPositiveHomologyEquivFullNegativeCycles (R := R) j d n
      ((AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).homologyπ (n + 1) z)).val e = _
  rw [positiveEquiv_projection]
  have h := ConcreteCategory.congr_hom
    (AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentHomology.MvPolynomial.coordinateFullNegativeHomologyProjection_homologyπ (R := R) j d n) z
  change (AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentHomology.MvPolynomial.coordinateFullNegativeHomologyProjection (R := R) j d n).hom
      ((AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).homologyπ (n + 1) z) =
    AlgebraicGeometry.SheafCohomology.Projective.LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection (R := R) d (n + 1)
      ((AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).iCycles (n + 1) z) at h
  rw [h]
  exact projection_top d (n + 1) hn _ e

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentTopCoordinates
