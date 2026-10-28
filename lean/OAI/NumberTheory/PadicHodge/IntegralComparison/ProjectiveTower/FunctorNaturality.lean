import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.PureDuality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.PureFunctorNaturality

/-! # Functor Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.FunctorNaturality

noncomputable section

/-! Projective pure Serre naturality on the actual cohomology-sheaf
functor, ready to descend through the common negative refinement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.PureDuality

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

variable {T T' : KernelTowerResolution.Tower (C := (Proj (homogeneousSubmodule σ R)).Modules)}
  [∀ i, (T.object i).IsQuasicoherent] [∀ i, (T'.object i).IsQuasicoherent]
  [∀ i, (T.term i).IsQuasicoherent] [∀ i, (T'.term i).IsQuasicoherent]
  [∀ i, (T.term i).IsFiniteType] [∀ i, (T'.term i).IsFiniteType]
  (B n : ℕ) (hn : Fintype.card σ = n + 2)
  (hT : ∀ i, NegativeTerms.Above (T.term i) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B)
  (hB : n + 2 ≤ B) (c : ℕ)
  (hPure : ∀ q, q ≠ c → (PureDuality.dualComplex T n hn).ExactAt q)
  (hT' : ∀ i, NegativeTerms.Above (T'.term i) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B)
  (hPure' : ∀ q, q ≠ c → (PureDuality.dualComplex T' n hn).ExactAt q)
  (a : KernelTowerMap.Hom T T')

@[reassoc]
abbrev naturality (i : ℕ) (hi : i + c ≤ n + 1) := by
  let (q : ℕ) : ((PureDuality.dualComplex T n hn).X q).IsQuasicoherent :=
    PureDuality.term_quasicoherent T B n hn hT hB q
  let (q : ℕ) : ((PureDuality.dualComplex T' n hn).X q).IsQuasicoherent :=
    PureDuality.term_quasicoherent T' B n hn hT' hB q
  let : Module.Injective (Projective.TopTracePairing.coefficientRing R) (Projective.TopTracePairing.coefficientRing R) :=
    Projective.SerreComplex.coefficient_injective
  have result := Trace.PureFunctorNaturality.naturality
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R)) (Projective.TopTracePairing.coefficientRing R)
    (Projective.TopTracePairing.topFunctor (R := R) (σ := σ) n) (Projective.TopTracePairing.canonicalTwist (R := R) n hn) (Projective.TopTracePairing.trace (R := R) n hn)
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))
    (fun q => Projective.TopDuality.pairing_bijective n hn (T.term q))
    (Total.terms_acyclic T B n hn hT hB) c hPure
    (fun q => Projective.TopDuality.pairing_bijective n hn (T'.term q))
    (Total.terms_acyclic T' B n hn hT' hB) hPure' a.chainMap i
    (Duality.cohomologyIso T n hn
      (Total.lower_vanishing T B n hn hT hB) (i + c) hi)
    (Duality.cohomologyIso T' n hn
      (Total.lower_vanishing T' B n hn hT' hB) (i + c) hi) _
    (CohomologyNaturality.naturality a n hn
      (Total.lower_vanishing T B n hn hT hB)
      (Total.lower_vanishing T' B n hn hT' hB) (i + c) hi)
  exact result

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.FunctorNaturality
