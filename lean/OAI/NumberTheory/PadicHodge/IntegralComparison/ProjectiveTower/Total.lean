import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.Duality
import OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTerms
import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.SerreTotal

/-! # Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.Total

noncomputable section

/-! The full projective Serre comparison for any negative kernel
tower, including the common refinements of the fixed resolutions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite

set_option backward.isDefEq.respectTransparency false

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

variable (T : KernelTowerResolution.Tower (C := (Proj (homogeneousSubmodule σ R)).Modules))
  [∀ i, (T.object i).IsQuasicoherent]
  [∀ i, (T.term i).IsQuasicoherent] [∀ i, (T.term i).IsFiniteType]
  (B n : ℕ) (hn : Fintype.card σ = n + 2)
  (hT : ∀ i, NegativeTerms.Above (T.term i) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B)
  (hB : n + 2 ≤ B)

include hT hB in
omit [IsNoetherianRing R] [∀ (i : ℕ), (T.object i).IsQuasicoherent] [∀ (i : ℕ), (T.term i).IsQuasicoherent] [∀ (i : ℕ), (T.term i).IsFiniteType] in
theorem lower_vanishing (q : ℕ) (hq : q < n + 1) (i : ℕ) :
    IsZero ((TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) q).obj (T.term i)) := by
  let : Nontrivial σ := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact NegativeTerms.lower_cohomology_zero (hT i) (by omega) q (by omega)

include hT hB in
omit [IsNoetherianRing R] [∀ (i : ℕ), (T.object i).IsQuasicoherent] [∀ (i : ℕ), (T.term i).IsQuasicoherent] [∀ (i : ℕ), (T.term i).IsFiniteType] in
theorem terms_acyclic :
    InternalHomCechTotal.TermsAcyclic (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (Projective.TopTracePairing.canonicalTwist (R := R) n hn) T.complex.op := by
  intro q p
  exact NegativeTerms.higher_dual_cohomology_zero (hT q) (n + 2) hB p

variable [Module.Injective R R]

def serreIso (d : ℕ) (hd : d ≤ n + 1) := by
  letI : Module.Injective (Projective.TopTracePairing.coefficientRing R) (Projective.TopTracePairing.coefficientRing R) :=
    Projective.SerreComplex.coefficient_injective
  exact Trace.SerreTotal.iso (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (Projective.TopTracePairing.coefficientRing R)
    (Projective.TopTracePairing.topFunctor (R := R) (σ := σ) n) (Projective.TopTracePairing.canonicalTwist (R := R) n hn)
    (Projective.TopTracePairing.trace (R := R) n hn) T.complex
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))
    (fun i => Projective.TopDuality.pairing_bijective n hn (T.term i))
    (terms_acyclic T B n hn hT hB) d
    (Duality.cohomologyIso T n hn (lower_vanishing T B n hn hT hB) d hd)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.Total
