import OAI.NumberTheory.PadicHodge.IntegralComparison.IndexedConcentrationTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.TotalTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.MixedPureSerreMap

/-! # Concentration Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.ConcentrationTrace

noncomputable section

/-! The actual projective total trace agrees with the pure Serre
trace through the original concentration isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.UnitTrace (cohomology)

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

variable (T : KernelTowerResolution.Tower (C := (Proj (homogeneousSubmodule σ R)).Modules))
  [∀ q, (T.object q).IsQuasicoherent]
  [∀ q, (T.term q).IsQuasicoherent] [∀ q, (T.term q).IsFiniteType]
  (B n : ℕ) (hn : Fintype.card σ = n + 2)
  (hT : ∀ q, NegativeTerms.Above (T.term q) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B)
  (hB : n + 2 ≤ B) (c : ℕ)
  (hPure : ∀ q, q ≠ c → (PureDuality.dualComplex T n hn).ExactAt q)

def concentration (i : ℕ) (hi : i + c = n + 1) := by
  let (q : ℕ) : ((PureDuality.dualComplex T n hn).X q).IsQuasicoherent :=
    PureDuality.term_quasicoherent T B n hn hT hB q
  exact MixedPureSerreMap.concentration
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R)) (Projective.TopTracePairing.canonicalTwist (R := R) n hn)
    T.complex c hPure i (n + 1) hi.symm

theorem trace (i : ℕ) (hi : i + c = n + 1) (v : UnitTrace.cohomology (T.object 0) 0) :
    (concentration T B n hn hT hB c hPure i hi).hom ≫
      UnitTrace.trace T B n hn hT hB c hPure i hi v =
    TotalTrace.trace T B n hn hT hB v := by
  let (q : ℕ) : ((PureDuality.dualComplex T n hn).X q).IsQuasicoherent :=
    PureDuality.term_quasicoherent T B n hn hT hB q
  exact IndexedConcentrationTrace.trace (Projective.TopTracePairing.coefficientRing R)
    (fun d => (InternalHomCechTotal.additiveTotal
      (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
      (Projective.TopTracePairing.canonicalTwist (R := R) n hn) T.complex.op).homology d)
    (UnitTrace.cohomology (T.object 0)) (n + 1) i c
    (fun d hd => Total.serreIso T B n hn hT hB d hd)
    (InternalHomCechConcentration.totalHomologyIso
      (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R)) (Projective.TopTracePairing.canonicalTwist (R := R) n hn)
      T.complex.op c hPure i) hi v

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.ConcentrationTrace
