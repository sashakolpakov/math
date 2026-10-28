import OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentTopCoordinates

/-! # Laurent Cohomology Residue -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentCohomologyResidue

noncomputable section

/-! Residues of actual top Čech cocycles compute the projective duality
pairing, and multiplication satisfies its cochain adjointness formula. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TwistResidueDuality OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentResiduePairing
  LaurentResidueNaturality LaurentPolynomialAction
  LaurentCechPolynomialAction LaurentTopCoordinates

universe u

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

def cohomologyDual (j : σ) (n m : ℕ) (hn : Fintype.card σ = n + 2) :
    (AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j
      (-(m : ℤ) - (Fintype.card σ : ℤ))).homology (n + 1) ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)]
        Module.Dual Γ(Spec (CommRingCat.of R), ⊤)
          (homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) m) :=
  (AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentTop.MvPolynomial.coordinateHomogeneousLaurentTopHomologyEquivCoefficients (R := R) j
    (-(m : ℤ) - (Fintype.card σ : ℤ)) n hn).trans
      (Projective.TwistResidueDuality.polynomialDual σ Γ(Spec (CommRingCat.of R), ⊤) m)

theorem cohomologyDual_cocycle (j : σ) (n m : ℕ) (hn : Fintype.card σ = n + 2)
    (z : (AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j
      (-(m : ℤ) - (Fintype.card σ : ℤ))).cycles (n + 1))
    (Q : homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) m) :
    cohomologyDual (R := R) j n m hn
      ((AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j
        (-(m : ℤ) - (Fintype.card σ : ℤ))).homologyπ (n + 1) z) Q =
    LaurentResiduePairing.residue σ Γ(Spec (CommRingCat.of R), ⊤)
      (LaurentResiduePairing.polynomialMap σ Γ(Spec (CommRingCat.of R), ⊤) Q.val *
        LaurentTopCoordinates.topAmbient (R := R) (-(m : ℤ) - (Fintype.card σ : ℤ)) (n + 1) hn
          ((AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j
            (-(m : ℤ) - (Fintype.card σ : ℤ))).iCycles (n + 1) z)) := by
  let d : ℤ := -(m : ℤ) - (Fintype.card σ : ℤ)
  have hcoords :
      AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentTop.MvPolynomial.coordinateHomogeneousLaurentTopHomologyEquivCoefficients (R := R) j d n hn
        ((AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).homologyπ (n + 1) z) =
      LaurentResidueNaturality.negativeCoefficients σ Γ(Spec (CommRingCat.of R), ⊤) m
        (LaurentTopCoordinates.topAmbient (R := R) d (n + 1) hn
          ((AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).iCycles (n + 1) z)) := by
    funext e
    exact LaurentTopCoordinates.homology_coordinates j d n hn z e
  change Projective.TwistResidueDuality.polynomialDual σ Γ(Spec (CommRingCat.of R), ⊤) m
    (AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentTop.MvPolynomial.coordinateHomogeneousLaurentTopHomologyEquivCoefficients (R := R) j d n hn
      ((AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).homologyπ (n + 1) z)) Q = _
  rw [hcoords]
  exact (LaurentResidueNaturality.residue_polynomial_mul σ Γ(Spec (CommRingCat.of R), ⊤) m Q _).symm

theorem topAmbient_objectMap (m : ℕ) (d : ℤ)
    (P : homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) m)
    (n : ℕ) (hn : Fintype.card σ = n + 1)
    (x : AlgebraicGeometry.SheafCohomology.Projective.LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n) :
    LaurentTopCoordinates.topAmbient (R := R) ((m : ℤ) + d) n hn ((LaurentCechPolynomialAction.objectMap (R := R) m d P n).hom x) =
      LaurentResiduePairing.polynomialMap σ Γ(Spec (CommRingCat.of R), ⊤) P.val * LaurentTopCoordinates.topAmbient (R := R) d n hn x := by
  have h := ConcreteCategory.congr_hom (LaurentCechPolynomialAction.objectMap_π (R := R) m d P n (LaurentTopCoordinates.topIndex n hn)) x
  change (Pi.π (LaurentCechPolynomialAction.Factor (R := R) ((m : ℤ) + d)) (LaurentTopCoordinates.topIndex n hn)).hom
      ((LaurentCechPolynomialAction.objectMap (R := R) m d P n).hom x) =
    LaurentPolynomialAction.polynomial Γ(Spec (CommRingCat.of R), ⊤) m d
      (fun k => ((LaurentTopCoordinates.topIndex.{u} (σ := σ) n hn).1 k).down) P
      ((Pi.π (LaurentCechPolynomialAction.Factor (R := R) d) (LaurentTopCoordinates.topIndex n hn)).hom x) at h
  change LaurentPolynomialAction.ambient Γ(Spec (CommRingCat.of R), ⊤) ((m : ℤ) + d)
    (fun k => ((LaurentTopCoordinates.topIndex.{u} (σ := σ) n hn).1 k).down)
    ((Pi.π (LaurentCechPolynomialAction.Factor (R := R) ((m : ℤ) + d)) (LaurentTopCoordinates.topIndex n hn)).hom
      ((LaurentCechPolynomialAction.objectMap (R := R) m d P n).hom x)) = _
  rw [h]
  exact LaurentPolynomialAction.ambient_polynomial Γ(Spec (CommRingCat.of R), ⊤) m d _ P _

theorem residue_objectMap (a b : ℕ) (d : ℤ)
    (P : homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) a)
    (Q : homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) b)
    (n : ℕ) (hn : Fintype.card σ = n + 1)
    (x : AlgebraicGeometry.SheafCohomology.Projective.LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n) :
    LaurentResiduePairing.residue σ Γ(Spec (CommRingCat.of R), ⊤)
      (LaurentResiduePairing.polynomialMap σ Γ(Spec (CommRingCat.of R), ⊤) Q.val *
        LaurentTopCoordinates.topAmbient (R := R) ((a : ℤ) + d) n hn ((LaurentCechPolynomialAction.objectMap (R := R) a d P n).hom x)) =
    LaurentResiduePairing.residue σ Γ(Spec (CommRingCat.of R), ⊤)
      (LaurentResiduePairing.polynomialMap σ Γ(Spec (CommRingCat.of R), ⊤)
          (LaurentResidueNaturality.homogeneousProduct σ Γ(Spec (CommRingCat.of R), ⊤) a b P Q).val *
        LaurentTopCoordinates.topAmbient (R := R) d n hn x) := by
  rw [topAmbient_objectMap]
  change LaurentResiduePairing.residue σ Γ(Spec (CommRingCat.of R), ⊤)
      (LaurentResiduePairing.polynomialMap σ Γ(Spec (CommRingCat.of R), ⊤) Q.val *
        (LaurentResiduePairing.polynomialMap σ Γ(Spec (CommRingCat.of R), ⊤) P.val * LaurentTopCoordinates.topAmbient (R := R) d n hn x)) =
    LaurentResiduePairing.residue σ Γ(Spec (CommRingCat.of R), ⊤)
      (LaurentResiduePairing.polynomialMap σ Γ(Spec (CommRingCat.of R), ⊤) (P.val * Q.val) *
        LaurentTopCoordinates.topAmbient (R := R) d n hn x)
  rw [map_mul (LaurentResiduePairing.polynomialMap σ Γ(Spec (CommRingCat.of R), ⊤)) P.val Q.val]
  congr 1
  ac_rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentCohomologyResidue
