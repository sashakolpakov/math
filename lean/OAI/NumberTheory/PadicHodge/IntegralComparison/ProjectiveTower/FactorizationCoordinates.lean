import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.FactorizationTrace

/-! # Factorization Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.FactorizationCoordinates

noncomputable section

/-! Unit-normalized traces descend along a specified map satisfying the common negative-tower square.
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

include hT hPureT in
theorem naturality
    (m : (PureDuality.dualComplex TB n hn).homology c ⟶ (PureDuality.dualComplex TA n hn).homology c)
    (hm : m ≫ HomologicalComplex.homologyMap
        ((Affine.LocalDualInvariance.functor (Projective.TopTracePairing.canonicalTwist (R := R) n hn)).map a.chainMap.op) c =
      HomologicalComplex.homologyMap
        ((Affine.LocalDualInvariance.functor (Projective.TopTracePairing.canonicalTwist (R := R) n hn)).map b.chainMap.op) c)
    (i : ℕ) (hi : i + c = n + 1)
    (v : UnitTrace.cohomology (T.object 0) 0) (vA : UnitTrace.cohomology (TA.object 0) 0) (vB : UnitTrace.cohomology (TB.object 0) 0)
    (ha : (TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) 0).map (a.object 0) v = vA)
    (hb : (TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) 0).map (b.object 0) v = vB) :
    (Trace.PureFunctorNaturality.cohomologyFunctor
      (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) i).map m ≫
        UnitTrace.trace TA B n hn hTA hB c hPureA i hi vA =
      UnitTrace.trace TB B n hn hTB hB c hPureB i hi vB :=
  FactorizationTrace.naturality B n hn hT hTA hTB hB c
    hPureT hPureA hPureB a b m hm i hi v vA vB ha hb

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.FactorizationCoordinates
