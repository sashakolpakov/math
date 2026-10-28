import OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistLaurentAction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TwistResidueCoordinates

/-! # Negative Twist Residue Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality

noncomputable section

/-! Actual maps between negative projective twists are adjoint to
homogeneous polynomial multiplication under the Čech residue pairing. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TwistResidueCoordinates OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentResiduePairing
  LaurentResidueNaturality NegativeTwistLaurentAction

universe u

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

def sheafMap (j : σ) (d e : ℤ)
    (f : AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d ⟶ AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j e) :
    Intrinsic.TwistResidueCoordinates.complex (R := R) j d ⟶ Intrinsic.TwistResidueCoordinates.complex (R := R) j e :=
  (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))).map f

omit [Fintype σ] in
@[reassoc]
theorem sheafMap_π (j : σ) (d e : ℤ)
    (f : AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d ⟶ AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j e)
    (n : ℕ) (a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :
    (sheafMap j d e f).f n ≫ Pi.π (Intrinsic.TwistResidueCoordinates.nativeFactor (R := R) j e) a =
      Pi.π (Intrinsic.TwistResidueCoordinates.nativeFactor (R := R) j d) a ≫
        ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).map f).app
          (op (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.val)) := by
  exact Limits.Pi.map_π
    (fun b : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).map f).app
        (op (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) b.val))) a

abbrev topChart (n : ℕ) (hn : Fintype.card σ = n + 1) : σ :=
  ((LaurentTopCoordinates.topIndex.{u} (σ := σ) n hn).val 0).down

omit [Fintype σ] in
theorem sheafMap_projection (j : σ) (d e : ℤ)
    (f : AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d ⟶ AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j e)
    (n : ℕ) (a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n)
    (x : (Intrinsic.TwistResidueCoordinates.complex (R := R) j d).X n) :
    (Pi.π (Intrinsic.TwistResidueCoordinates.nativeFactor (R := R) j e) a).hom ((sheafMap j d e f).f n x) =
      f.app (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.val)
        ((Pi.π (Intrinsic.TwistResidueCoordinates.nativeFactor (R := R) j d) a).hom x) := by
  exact ConcreteCategory.congr_hom (sheafMap_π j d e f n a) x

theorem topAmbient_sheafMap_of_action (j : σ) (d e : ℤ) (n : ℕ)
    (hn : Fintype.card σ = n + 1) (m : ℕ)
    (P : homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) m)
    (f : AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d ⟶ AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j e)
    (hf : ∀ y : Γ(AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d,
      AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) (LaurentTopCoordinates.topIndex.{u} n hn).val),
      LaurentPolynomialAction.ambient Γ(Spec (CommRingCat.of R), ⊤) e
          (fun k => ((LaurentTopCoordinates.topIndex.{u} (σ := σ) n hn).val k).down)
          (Projective.SectionIntersections.coordinates (R := R) j e
            (LaurentTopCoordinates.topIndex.{u} n hn)
            (f.app (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R)
              (LaurentTopCoordinates.topIndex.{u} n hn).val) y)) =
        LaurentResiduePairing.polynomialMap σ Γ(Spec (CommRingCat.of R), ⊤) P.val *
          LaurentPolynomialAction.ambient Γ(Spec (CommRingCat.of R), ⊤) d
            (fun k => ((LaurentTopCoordinates.topIndex.{u} (σ := σ) n hn).val k).down)
            (Projective.SectionIntersections.coordinates (R := R) j d
              (LaurentTopCoordinates.topIndex.{u} n hn) y))
    (x : (Intrinsic.TwistResidueCoordinates.complex (R := R) j d).X n) :
    Intrinsic.TwistResidueCoordinates.topAmbient (R := R) j e n hn ((sheafMap j d e f).f n x) =
      LaurentResiduePairing.polynomialMap σ Γ(Spec (CommRingCat.of R), ⊤) P.val *
        Intrinsic.TwistResidueCoordinates.topAmbient (R := R) j d n hn x := by
  rw [Intrinsic.TwistResidueCoordinates.topAmbient_projection, Intrinsic.TwistResidueCoordinates.topAmbient_projection, sheafMap_projection]
  exact hf _

set_option backward.isDefEq.respectTransparency true in
attribute [local irreducible] AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials
  LaurentPolynomialAction.ambient Projective.SectionIntersections.coordinates
  Intrinsic.TwistResidueCoordinates.topAmbient LaurentResiduePairing.polynomialMap in
theorem topAmbient_sheafMap (n : ℕ) (hn : Fintype.card σ = n + 1)
    (A B : ℕ) (hBA : B ≤ A)
    (f : AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (topChart.{u} n hn) (A + 1) ⟶
      AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (topChart.{u} n hn) (B + 1))
    (x : (Intrinsic.TwistResidueCoordinates.complex (R := R) (topChart.{u} n hn) (.negSucc A)).X n) :
    Intrinsic.TwistResidueCoordinates.topAmbient (R := R) (topChart.{u} n hn) (.negSucc B) n hn
      ((sheafMap (topChart.{u} n hn) (.negSucc A) (.negSucc B) f).f n x) =
      LaurentResiduePairing.polynomialMap σ Γ(Spec (CommRingCat.of R), ⊤)
          (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials (R := R) (topChart.{u} n hn)
            (A + 1) (B + 1) (Nat.add_le_add_right hBA 1) f).val *
        Intrinsic.TwistResidueCoordinates.topAmbient (R := R) (topChart.{u} n hn) (.negSucc A) n hn x := by
  refine topAmbient_sheafMap_of_action (R := R) (topChart.{u} n hn) (.negSucc A) (.negSucc B)
    n hn ((A + 1) - (B + 1))
    (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials (R := R) (topChart.{u} n hn)
      (A + 1) (B + 1) (Nat.add_le_add_right hBA 1) f) f ?_ x
  intro y
  exact NegativeTwistLaurentAction.native_laurent_action_at_chart (R := R) (topChart.{u} n hn) A B hBA
    (LaurentTopCoordinates.topIndex.{u} (σ := σ) n hn) rfl f y

theorem cohomologyDual_naturality_of_topAmbient (j : σ) (d e : ℤ) (n a b : ℕ)
    (hn : Fintype.card σ = n + 2)
    (hd : d = -((a + b : ℕ) : ℤ) - (Fintype.card σ : ℤ))
    (he : e = -(b : ℤ) - (Fintype.card σ : ℤ))
    (P : homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) a)
    (f : Intrinsic.TwistResidueCoordinates.complex (R := R) j d ⟶ Intrinsic.TwistResidueCoordinates.complex (R := R) j e)
    (hf : ∀ y : (Intrinsic.TwistResidueCoordinates.complex (R := R) j d).X (n + 1),
      Intrinsic.TwistResidueCoordinates.topAmbient (R := R) j e (n + 1) hn (f.f (n + 1) y) =
        LaurentResiduePairing.polynomialMap σ Γ(Spec (CommRingCat.of R), ⊤) P.val *
          Intrinsic.TwistResidueCoordinates.topAmbient (R := R) j d (n + 1) hn y)
    (Q : homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) b)
    (x : (Intrinsic.TwistResidueCoordinates.complex (R := R) j d).homology (n + 1)) :
    Intrinsic.TwistResidueCoordinates.cohomologyDual (R := R) j e n b hn he
      ((HomologicalComplex.homologyMap f (n + 1)).hom x) Q =
      Intrinsic.TwistResidueCoordinates.cohomologyDual (R := R) j d n (a + b) hn hd x
        (LaurentResidueNaturality.homogeneousProduct σ Γ(Spec (CommRingCat.of R), ⊤) a b P Q) := by
  let K := Intrinsic.TwistResidueCoordinates.complex (R := R) j d
  let L := Intrinsic.TwistResidueCoordinates.complex (R := R) j e
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ (n + 1))).mp inferInstance x
  have hπ := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality f (n + 1)) z
  change (HomologicalComplex.homologyMap f (n + 1)).hom (K.homologyπ (n + 1) z) =
    L.homologyπ (n + 1) (HomologicalComplex.cyclesMap f (n + 1) z) at hπ
  rw [hπ, Intrinsic.TwistResidueCoordinates.cohomologyDual_cocycle, Intrinsic.TwistResidueCoordinates.cohomologyDual_cocycle]
  have hi := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i f (n + 1)) z
  change L.iCycles (n + 1) (HomologicalComplex.cyclesMap f (n + 1) z) =
    f.f (n + 1) (K.iCycles (n + 1) z) at hi
  rw [hi, hf]
  change LaurentResiduePairing.residue σ Γ(Spec (CommRingCat.of R), ⊤)
      (LaurentResiduePairing.polynomialMap σ Γ(Spec (CommRingCat.of R), ⊤) Q.val *
        (LaurentResiduePairing.polynomialMap σ Γ(Spec (CommRingCat.of R), ⊤) P.val *
          Intrinsic.TwistResidueCoordinates.topAmbient (R := R) j d (n + 1) hn (K.iCycles (n + 1) z))) =
    LaurentResiduePairing.residue σ Γ(Spec (CommRingCat.of R), ⊤)
      (LaurentResiduePairing.polynomialMap σ Γ(Spec (CommRingCat.of R), ⊤) (P.val * Q.val) *
        Intrinsic.TwistResidueCoordinates.topAmbient (R := R) j d (n + 1) hn (K.iCycles (n + 1) z))
  rw [map_mul (LaurentResiduePairing.polynomialMap σ Γ(Spec (CommRingCat.of R), ⊤)) P.val Q.val]
  congr 1
  ac_rfl

omit [LinearOrder σ] in
theorem negative_degree (A B b : ℕ) (hBA : B ≤ A)
    (hb : Int.negSucc B = -(b : ℤ) - (Fintype.card σ : ℤ)) :
    Int.negSucc A = -((((A + 1) - (B + 1) + b : ℕ)) : ℤ) - (Fintype.card σ : ℤ) := by
  omega

set_option backward.isDefEq.respectTransparency true in
attribute [local irreducible] AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials in
theorem cohomologyDual_naturality (n : ℕ) (hn : Fintype.card σ = n + 2)
    (A B b : ℕ) (hBA : B ≤ A)
    (hb : Int.negSucc B = -(b : ℤ) - (Fintype.card σ : ℤ))
    (f : AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (topChart.{u} (n + 1) hn) (A + 1) ⟶
      AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (topChart.{u} (n + 1) hn) (B + 1))
    (Q : homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) b)
    (x : (Intrinsic.TwistResidueCoordinates.complex (R := R) (topChart.{u} (n + 1) hn) (.negSucc A)).homology (n + 1)) :
    Intrinsic.TwistResidueCoordinates.cohomologyDual (R := R) (topChart.{u} (n + 1) hn) (.negSucc B) n b hn hb
      ((HomologicalComplex.homologyMap
        (sheafMap (topChart.{u} (n + 1) hn) (.negSucc A) (.negSucc B) f) (n + 1)).hom x) Q =
      Intrinsic.TwistResidueCoordinates.cohomologyDual (R := R) (topChart.{u} (n + 1) hn) (.negSucc A) n
        ((A + 1) - (B + 1) + b) hn (negative_degree A B b hBA hb) x
        (LaurentResidueNaturality.homogeneousProduct σ Γ(Spec (CommRingCat.of R), ⊤) ((A + 1) - (B + 1)) b
          (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials (R := R) (topChart.{u} (n + 1) hn)
            (A + 1) (B + 1) (Nat.add_le_add_right hBA 1) f) Q) := by
  let P := AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials (R := R) (topChart.{u} (n + 1) hn)
    (A + 1) (B + 1) (Nat.add_le_add_right hBA 1) f
  have htop := topAmbient_sheafMap (R := R) (n + 1) hn A B hBA f
  have hnat := cohomologyDual_naturality_of_topAmbient (R := R)
    (topChart.{u} (n + 1) hn) (.negSucc A) (.negSucc B)
    n ((A + 1) - (B + 1)) b hn (negative_degree A B b hBA hb) hb P
    (sheafMap (topChart.{u} (n + 1) hn) (.negSucc A) (.negSucc B) f) htop Q x
  exact hnat

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality
