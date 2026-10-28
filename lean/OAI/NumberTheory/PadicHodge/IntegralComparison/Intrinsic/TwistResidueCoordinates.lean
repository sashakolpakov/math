import OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentCohomologyResidue
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SectionIntersections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor

/-! # Twist Residue Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TwistResidueCoordinates

noncomputable section

/-! The Laurent residue pairing on the original ordered Čech complex of
a projective twist, with its value on native cocycles made explicit. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentPolynomialAction OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentCechPolynomialAction
  LaurentResiduePairing Projective.SectionIntersections

universe u

theorem piIso_comp_π {C : Type*} [Category C] {ι : Type*}
    {F G H : ι → C} [HasProductsOfShape ι C]
    (e : ∀ i, F i ≅ G i) (f : ∀ i, G i ≅ H i) (i : ι) :
    ((Pi.mapIso e).hom ≫ (Pi.mapIso f).hom) ≫ Pi.π H i =
      Pi.π F i ≫ (e i ≪≫ f i).hom := by
  rw [Category.assoc, Pi.mapIso_hom_π, Pi.mapIso_hom_π_assoc]
  rfl

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev complex (j : σ) (d : ℤ) :=
  AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))

def laurentIso (j : σ) (d : ℤ) :
    complex (R := R) j d ≅ AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d :=
  AlgebraicGeometry.SheafCohomology.Projective.TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechComplexIso (R := R) j d ≪≫
    AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplexIso (R := R) j d

abbrev nativeFactor (j : σ) (d : ℤ) {n : ℕ}
    (a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :=
  AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n a.val

omit [Fintype σ] in
@[reassoc]
theorem laurentIso_π (j : σ) (d : ℤ) (n : ℕ)
    (a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :
    (laurentIso (R := R) j d).hom.f n ≫ Pi.π (LaurentCechPolynomialAction.Factor (R := R) d) a =
      Pi.π (nativeFactor (R := R) j d) a ≫ (Projective.SectionIntersections.coordinates (R := R) j d a).toModuleIso.hom := by
  exact piIso_comp_π
    (fun b : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      AlgebraicGeometry.SheafCohomology.Projective.TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) b.val j d)
    (fun b : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv (R := R) b.val d).toModuleIso) a

def topAmbient (j : σ) (d : ℤ) (n : ℕ) (hn : Fintype.card σ = n + 1) :
    (complex (R := R) j d).X n →ₗ[Γ(Spec (CommRingCat.of R), ⊤)]
      AddMonoidAlgebra Γ(Spec (CommRingCat.of R), ⊤) (σ →₀ ℤ) :=
  (LaurentTopCoordinates.topAmbient (R := R) d n hn).comp
    ((laurentIso (R := R) j d).hom.f n).hom

theorem topAmbient_projection (j : σ) (d : ℤ) (n : ℕ) (hn : Fintype.card σ = n + 1)
    (x : (complex (R := R) j d).X n) :
    topAmbient (R := R) j d n hn x =
      LaurentPolynomialAction.ambient Γ(Spec (CommRingCat.of R), ⊤) d
        (fun k => ((LaurentTopCoordinates.topIndex.{u} (σ := σ) n hn).val k).down)
        (Projective.SectionIntersections.coordinates (R := R) j d (LaurentTopCoordinates.topIndex n hn)
          ((Pi.π (nativeFactor (R := R) j d) (LaurentTopCoordinates.topIndex n hn)).hom x)) := by
  have h := ConcreteCategory.congr_hom
    (laurentIso_π (R := R) j d n (LaurentTopCoordinates.topIndex n hn)) x
  exact congrArg (LaurentPolynomialAction.ambient Γ(Spec (CommRingCat.of R), ⊤) d
    (fun k => ((LaurentTopCoordinates.topIndex.{u} (σ := σ) n hn).val k).down)) h

def laurentDual (j : σ) (d : ℤ) (n m : ℕ) (hn : Fintype.card σ = n + 2)
    (hd : d = -(m : ℤ) - (Fintype.card σ : ℤ)) :
    (AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).homology (n + 1) ≃ₗ[
      Γ(Spec (CommRingCat.of R), ⊤)]
        Module.Dual Γ(Spec (CommRingCat.of R), ⊤)
          (homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) m) := by
  subst d
  exact LaurentCohomologyResidue.cohomologyDual j n m hn

theorem laurentDual_cocycle (j : σ) (d : ℤ) (n m : ℕ) (hn : Fintype.card σ = n + 2)
    (hd : d = -(m : ℤ) - (Fintype.card σ : ℤ))
    (z : (AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).cycles (n + 1))
    (Q : homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) m) :
    laurentDual (R := R) j d n m hn hd
      ((AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).homologyπ (n + 1) z) Q =
      LaurentResiduePairing.residue σ Γ(Spec (CommRingCat.of R), ⊤)
        (LaurentResiduePairing.polynomialMap σ Γ(Spec (CommRingCat.of R), ⊤) Q.val *
          LaurentTopCoordinates.topAmbient (R := R) d (n + 1) hn
            ((AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).iCycles (n + 1) z)) := by
  subst d
  exact LaurentCohomologyResidue.cohomologyDual_cocycle j n m hn z Q

def cohomologyDual (j : σ) (d : ℤ) (n m : ℕ) (hn : Fintype.card σ = n + 2)
    (hd : d = -(m : ℤ) - (Fintype.card σ : ℤ)) :
    (complex (R := R) j d).homology (n + 1) ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)]
      Module.Dual Γ(Spec (CommRingCat.of R), ⊤)
        (homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) m) :=
  (HomologicalComplex.homologyMapIso (laurentIso (R := R) j d) (n + 1)).toLinearEquiv.trans
    (laurentDual j d n m hn hd)

theorem cohomologyDual_cocycle (j : σ) (d : ℤ) (n m : ℕ) (hn : Fintype.card σ = n + 2)
    (hd : d = -(m : ℤ) - (Fintype.card σ : ℤ))
    (z : (complex (R := R) j d).cycles (n + 1))
    (Q : homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) m) :
    cohomologyDual (R := R) j d n m hn hd ((complex (R := R) j d).homologyπ (n + 1) z) Q =
      LaurentResiduePairing.residue σ Γ(Spec (CommRingCat.of R), ⊤)
        (LaurentResiduePairing.polynomialMap σ Γ(Spec (CommRingCat.of R), ⊤) Q.val *
          topAmbient (R := R) j d (n + 1) hn ((complex (R := R) j d).iCycles (n + 1) z)) := by
  let K := complex (R := R) j d
  let L := AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d
  let f : K ⟶ L := (laurentIso (R := R) j d).hom
  have hπ := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality f (n + 1)) z
  change (HomologicalComplex.homologyMap f (n + 1)).hom (K.homologyπ (n + 1) z) =
    L.homologyπ (n + 1) (HomologicalComplex.cyclesMap f (n + 1) z) at hπ
  change laurentDual (R := R) j d n m hn hd
    ((HomologicalComplex.homologyMap f (n + 1)).hom (K.homologyπ (n + 1) z)) Q = _
  rw [hπ, laurentDual_cocycle]
  have hi := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i f (n + 1)) z
  exact congrArg (fun y : L.X (n + 1) => LaurentResiduePairing.residue σ Γ(Spec (CommRingCat.of R), ⊤)
    (LaurentResiduePairing.polynomialMap σ Γ(Spec (CommRingCat.of R), ⊤) Q.val *
      LaurentTopCoordinates.topAmbient (R := R) d (n + 1) hn y)) hi

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TwistResidueCoordinates
