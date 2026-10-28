import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.UnitTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.PureUnitRefinement

/-! # Refinement Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.RefinementTrace

noncomputable section

/-! Unit-normalized traces descend through a common negative tower.
The statement allows distinct degree-zero objects and only asks that
the two actual tower maps carry the specified class to each target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.PureDuality OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.UnitTrace

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

variable {T TA TB : KernelTowerResolution.Tower (C := (Proj (homogeneousSubmodule σ R)).Modules)}
  [∀ q, (T.object q).IsQuasicoherent] [∀ q, (TA.object q).IsQuasicoherent]
  [∀ q, (TB.object q).IsQuasicoherent]
  [∀ q, (T.term q).IsQuasicoherent] [∀ q, (TA.term q).IsQuasicoherent]
  [∀ q, (TB.term q).IsQuasicoherent]
  [∀ q, (T.term q).IsFiniteType] [∀ q, (TA.term q).IsFiniteType] [∀ q, (TB.term q).IsFiniteType]
  (B n : ℕ) (hn : Fintype.card σ = n + 2)
  (hT : ∀ q, NegativeTerms.Above (T.term q) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B)
  (hTA : ∀ q, NegativeTerms.Above (TA.term q) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B)
  (hTB : ∀ q, NegativeTerms.Above (TB.term q) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B)
  (hB : n + 2 ≤ B) (c : ℕ)
  (hPureT : ∀ q, q ≠ c → (PureDuality.dualComplex T n hn).ExactAt q)
  (hPureA : ∀ q, q ≠ c → (PureDuality.dualComplex TA n hn).ExactAt q)
  (hPureB : ∀ q, q ≠ c → (PureDuality.dualComplex TB n hn).ExactAt q)
  (a : KernelTowerMap.Hom T TA) (b : KernelTowerMap.Hom T TB)
  [IsIso (HomologicalComplex.homologyMap
    ((Affine.LocalDualInvariance.functor (Projective.TopTracePairing.canonicalTwist (R := R) n hn)).map a.chainMap.op) c)]

include hT hPureT in
theorem naturality (i : ℕ) (hi : i + c = n + 1)
    (v : UnitTrace.cohomology (T.object 0) 0) (vA : UnitTrace.cohomology (TA.object 0) 0) (vB : UnitTrace.cohomology (TB.object 0) 0)
    (ha : (TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) 0).map (a.object 0) v = vA)
    (hb : (TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) 0).map (b.object 0) v = vB) :
    (Trace.PureFunctorNaturality.cohomologyFunctor
      (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) i).map
        (Trace.PureRefinement.map (Projective.TopTracePairing.canonicalTwist (R := R) n hn) a.chainMap b.chainMap c) ≫
      UnitTrace.trace TA B n hn hTA hB c hPureA i hi vA =
    UnitTrace.trace TB B n hn hTB hB c hPureB i hi vB := by
  let (q : ℕ) : ((PureDuality.dualComplex T n hn).X q).IsQuasicoherent :=
    PureDuality.term_quasicoherent T B n hn hT hB q
  let (q : ℕ) : ((PureDuality.dualComplex TA n hn).X q).IsQuasicoherent :=
    PureDuality.term_quasicoherent TA B n hn hTA hB q
  let (q : ℕ) : ((PureDuality.dualComplex TB n hn).X q).IsQuasicoherent :=
    PureDuality.term_quasicoherent TB B n hn hTB hB q
  let : Module.Injective (Projective.TopTracePairing.coefficientRing R) (Projective.TopTracePairing.coefficientRing R) :=
    Projective.SerreComplex.coefficient_injective
  exact Trace.PureUnitRefinement.naturality
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R)) (Projective.TopTracePairing.coefficientRing R)
    (Projective.TopTracePairing.topFunctor (R := R) (σ := σ) n) (Projective.TopTracePairing.canonicalTwist (R := R) n hn)
    (Projective.TopTracePairing.trace (R := R) n hn)
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))
    (fun q => Projective.TopDuality.pairing_bijective n hn (T.term q))
    (Total.terms_acyclic T B n hn hT hB) c hPureT
    (fun q => Projective.TopDuality.pairing_bijective n hn (TA.term q))
    (Total.terms_acyclic TA B n hn hTA hB) hPureA
    (fun q => Projective.TopDuality.pairing_bijective n hn (TB.term q))
    (Total.terms_acyclic TB B n hn hTB hB) hPureB
    a.chainMap b.chainMap i (n + 1 - (i + c))
    (UnitTrace.cohomology (T.object 0)) (UnitTrace.cohomology (TA.object 0)) (UnitTrace.cohomology (TB.object 0))
    (Duality.cohomologyIso T n hn
      (Total.lower_vanishing T B n hn hT hB) (i + c) hi.le)
    (Duality.cohomologyIso TA n hn
      (Total.lower_vanishing TA B n hn hTA hB) (i + c) hi.le)
    (Duality.cohomologyIso TB n hn
      (Total.lower_vanishing TB B n hn hTB hB) (i + c) hi.le)
    (by omega)
    (fun j => (TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) j).map (a.object 0))
    (fun j => (TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) j).map (b.object 0))
    (CohomologyNaturality.naturality a n hn
      (Total.lower_vanishing T B n hn hT hB)
      (Total.lower_vanishing TA B n hn hTA hB) (i + c) hi.le)
    (CohomologyNaturality.naturality b n hn
      (Total.lower_vanishing T B n hn hT hB)
      (Total.lower_vanishing TB B n hn hTB hB) (i + c) hi.le)
    v vA vB ha hb

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.RefinementTrace
