import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.FunctorNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.PureUnitNaturality

/-! # Unit Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.UnitTrace

noncomputable section

/-! The pure projective Serre pairing evaluated on a degree-zero
class is natural under actual maps of negative resolutions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.PureDuality

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

def cohomology (M : (Proj (homogeneousSubmodule σ R)).Modules) (i : ℕ) :
    ModuleCat.{u} (Projective.TopTracePairing.coefficientRing R) :=
  (TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) i).obj M

variable (T : KernelTowerResolution.Tower (C := (Proj (homogeneousSubmodule σ R)).Modules))
  [∀ q, (T.object q).IsQuasicoherent]
  [∀ q, (T.term q).IsQuasicoherent] [∀ q, (T.term q).IsFiniteType]
  (B n : ℕ) (hn : Fintype.card σ = n + 2)
  (hT : ∀ q, NegativeTerms.Above (T.term q) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B)
  (hB : n + 2 ≤ B) (c : ℕ)
  (hPure : ∀ q, q ≠ c → (PureDuality.dualComplex T n hn).ExactAt q)

def pairing (i : ℕ) (hi : i + c = n + 1) :=
  IndexedSerreUnitTrace.pairing (Projective.TopTracePairing.coefficientRing R) (cohomology (T.object 0))
    (PureDuality.iso T B n hn hT hB c hPure i hi.le) (by omega)

def trace (i : ℕ) (hi : i + c = n + 1) (v : cohomology (T.object 0) 0) :=
  SerreUnitTrace.trace (Projective.TopTracePairing.coefficientRing R) (pairing T B n hn hT hB c hPure i hi) v

variable {T}
  {T' : KernelTowerResolution.Tower (C := (Proj (homogeneousSubmodule σ R)).Modules)}
  [∀ q, (T'.object q).IsQuasicoherent]
  [∀ q, (T'.term q).IsQuasicoherent] [∀ q, (T'.term q).IsFiniteType]
  (hT' : ∀ q, NegativeTerms.Above (T'.term q) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B)
  (hPure' : ∀ q, q ≠ c → (PureDuality.dualComplex T' n hn).ExactAt q)
  (a : KernelTowerMap.Hom T T')

theorem naturality (i : ℕ) (hi : i + c = n + 1)
    (v : cohomology (T.object 0) 0) (v' : cohomology (T'.object 0) 0)
    (hv : (TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) 0).map (a.object 0) v = v') :
    (Trace.PureFunctorNaturality.cohomologyFunctor
      (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) i).map
        (HomologicalComplex.homologyMap
          ((Affine.LocalDualInvariance.functor (Projective.TopTracePairing.canonicalTwist (R := R) n hn)).map a.chainMap.op) c) ≫
      trace T B n hn hT hB c hPure i hi v =
    trace T' B n hn hT' hB c hPure' i hi v' := by
  let (q : ℕ) : ((PureDuality.dualComplex T n hn).X q).IsQuasicoherent :=
    PureDuality.term_quasicoherent T B n hn hT hB q
  let (q : ℕ) : ((PureDuality.dualComplex T' n hn).X q).IsQuasicoherent :=
    PureDuality.term_quasicoherent T' B n hn hT' hB q
  let : Module.Injective (Projective.TopTracePairing.coefficientRing R) (Projective.TopTracePairing.coefficientRing R) :=
    Projective.SerreComplex.coefficient_injective
  exact Trace.PureUnitNaturality.naturality
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R)) (Projective.TopTracePairing.coefficientRing R)
    (Projective.TopTracePairing.topFunctor (R := R) (σ := σ) n) (Projective.TopTracePairing.canonicalTwist (R := R) n hn)
    (Projective.TopTracePairing.trace (R := R) n hn)
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))
    (fun q => Projective.TopDuality.pairing_bijective n hn (T.term q))
    (Total.terms_acyclic T B n hn hT hB) c hPure
    (fun q => Projective.TopDuality.pairing_bijective n hn (T'.term q))
    (Total.terms_acyclic T' B n hn hT' hB) hPure' a.chainMap i (n + 1 - (i + c))
    (cohomology (T.object 0)) (cohomology (T'.object 0))
    (Duality.cohomologyIso T n hn
      (Total.lower_vanishing T B n hn hT hB) (i + c) hi.le)
    (Duality.cohomologyIso T' n hn
      (Total.lower_vanishing T' B n hn hT' hB) (i + c) hi.le)
    (by omega)
    (fun j => (TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) j).map (a.object 0))
    (CohomologyNaturality.naturality a n hn
      (Total.lower_vanishing T B n hn hT hB)
      (Total.lower_vanishing T' B n hn hT' hB) (i + c) hi.le)
    v v' hv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.UnitTrace
