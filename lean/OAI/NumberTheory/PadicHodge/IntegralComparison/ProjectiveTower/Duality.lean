import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SerreComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomTotalTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.DualHomologyTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.DualityHomology

/-! # Duality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.Duality

noncomputable section

/-! The projective residue pairing applies to arbitrary coherent
kernel towers with vanishing lower term cohomology. This includes the
common negative refinements used for functoriality. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite

set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

variable (T : KernelTowerResolution.Tower (C := (Proj (homogeneousSubmodule σ R)).Modules))
  [∀ i, (T.object i).IsQuasicoherent]
  [∀ i, (T.term i).IsQuasicoherent] [∀ i, (T.term i).IsFiniteType]
  (n : ℕ) (hn : Fintype.card σ = n + 2)

abbrev topComplex :=
  KernelTowerCechHomology.complex (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) T (n + 1)

abbrev homComplex :=
  Trace.DualityHomology.homComplex (ω := Projective.TopTracePairing.canonicalTwist (R := R) n hn) T.complex

def complexIso : homComplex T n hn ≅
    ((Trace.DualityComplex.dualFunctor (Projective.TopTracePairing.coefficientRing R)
      (Projective.TopTracePairing.topFunctor (R := R) (σ := σ) n)).mapHomologicalComplex
        (.up ℕ)).obj T.complex.op :=
  Trace.DualityComplex.complexIso (Projective.TopTracePairing.coefficientRing R)
    (Projective.TopTracePairing.topFunctor (R := R) (σ := σ) n) (Projective.TopTracePairing.trace (R := R) n hn)
    (.up ℕ) T.complex.op
    (fun i => Projective.TopDuality.pairing_bijective n hn (T.term i))

def zeroIso : (topComplex T n).homology 0 ≅
    (Projective.TopTracePairing.topFunctor (R := R) (σ := σ) n).obj (T.object 0) :=
  KernelTowerCechHomology.zeroIso (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R))
    T (n + 1) (by simpa using hn.le)

def cohomologyIso
    (hT : ∀ q < n + 1, ∀ i, IsZero
      ((TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) q).obj (T.term i)))
    : ∀ (d : ℕ), d ≤ n + 1 →
    ((topComplex T n).homology d ≅
      (TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (n + 1 - d)).obj (T.object 0))
  | 0, _ => zeroIso T n hn
  | i + 1, hd => by
    have hi : i ≤ n := by omega
    have hi' : n - i + i = n := Nat.sub_add_cancel hi
    have hs : n + 1 = n - i + i + 1 := by omega
    have ht : n - i = n + 1 - (i + 1) := by omega
    exact eqToIso (congrArg (fun r =>
      (KernelTowerCechHomology.complex (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) T r).homology (i + 1)) hs) ≪≫
      KernelTowerCechHomology.shiftedPositiveIso (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R))
        T (n - i) i (by simpa [hi'] using hn.le)
        (fun q hq j => hT q (by omega) j) ≪≫
      eqToIso (congrArg (fun r =>
        (TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
          (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) r).obj (T.object 0)) ht)

variable [Module.Injective R R]

def homologyDualIso (d : ℕ) : (homComplex T n hn).homology d ≅
    AddCommGrpCat.of (Module.Dual (Projective.TopTracePairing.coefficientRing R) ((topComplex T n).homology d)) := by
  letI : Module.Injective (Projective.TopTracePairing.coefficientRing R) (Projective.TopTracePairing.coefficientRing R) :=
    Projective.SerreComplex.coefficient_injective
  exact Trace.DualityHomology.homologyIso (Projective.TopTracePairing.coefficientRing R)
    (Projective.TopTracePairing.topFunctor (R := R) (σ := σ) n) (Projective.TopTracePairing.trace (R := R) n hn) T.complex
    (fun i => Projective.TopDuality.pairing_bijective n hn (T.term i)) d

def complementaryCohomology (d : ℕ) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (Module.Dual (Projective.TopTracePairing.coefficientRing R)
    ((TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (n + 1 - d)).obj (T.object 0)))

def serreIso
    (hT : ∀ q < n + 1, ∀ i, IsZero
      ((TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) q).obj (T.term i)))
    (d : ℕ) (hd : d ≤ n + 1) := by
  letI : Module.Injective (Projective.TopTracePairing.coefficientRing R) (Projective.TopTracePairing.coefficientRing R) :=
    Projective.SerreComplex.coefficient_injective
  exact Trace.DualityHomology.homologyIsoTo (Projective.TopTracePairing.coefficientRing R)
    (Projective.TopTracePairing.topFunctor (R := R) (σ := σ) n) (Projective.TopTracePairing.trace (R := R) n hn) T.complex
    (fun i => Projective.TopDuality.pairing_bijective n hn (T.term i)) d
    (cohomologyIso T n hn hT d hd)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.Duality
