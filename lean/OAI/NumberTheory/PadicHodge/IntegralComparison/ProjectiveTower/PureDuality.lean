import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.SerreNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomConcentrationNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.PureSerre

/-! # Pure Duality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.PureDuality

noncomputable section

/-! Projective Serre duality and its naturality on the actual surviving
cohomology sheaf of a pure negative resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

variable (T : KernelTowerResolution.Tower (C := (Proj (homogeneousSubmodule σ R)).Modules))
  [∀ i, (T.object i).IsQuasicoherent]
  [∀ i, (T.term i).IsQuasicoherent] [∀ i, (T.term i).IsFiniteType]
  (B n : ℕ) (hn : Fintype.card σ = n + 2)
  (hT : ∀ i, NegativeTerms.Above (T.term i) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B)
  (hB : n + 2 ≤ B)

abbrev dualComplex :=
  InternalHomCechTotal.internalComplex (Projective.TopTracePairing.canonicalTwist (R := R) n hn) T.complex.op

omit [IsNoetherianRing R] [Module.Injective R R] [∀ i, (T.object i).IsQuasicoherent]
  [∀ i, (T.term i).IsQuasicoherent] [∀ i, (T.term i).IsFiniteType] in
include hT hB in
theorem term_quasicoherent (q : ℕ) : ((dualComplex T n hn).X q).IsQuasicoherent :=
  NegativeTerms.dual_quasicoherent (hT q) (n + 2) hB

variable (c : ℕ) (hPure : ∀ q, q ≠ c → (dualComplex T n hn).ExactAt q)

def iso (i : ℕ) (hi : i + c ≤ n + 1) := by
  let (q : ℕ) : ((dualComplex T n hn).X q).IsQuasicoherent :=
    term_quasicoherent T B n hn hT hB q
  letI : Module.Injective (Projective.TopTracePairing.coefficientRing R) (Projective.TopTracePairing.coefficientRing R) :=
    Projective.SerreComplex.coefficient_injective
  exact Trace.PureSerre.iso (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R))
    (Projective.TopTracePairing.coefficientRing R) (Projective.TopTracePairing.topFunctor (R := R) (σ := σ) n) (Projective.TopTracePairing.canonicalTwist (R := R) n hn)
    (Projective.TopTracePairing.trace (R := R) n hn) T.complex (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))
    (fun q => Projective.TopDuality.pairing_bijective n hn (T.term q))
    (Total.terms_acyclic T B n hn hT hB) c hPure i
    (Duality.cohomologyIso T n hn
      (Total.lower_vanishing T B n hn hT hB) (i + c) hi)

variable {T} {T' : KernelTowerResolution.Tower (C := (Proj (homogeneousSubmodule σ R)).Modules)}
  [∀ i, (T'.object i).IsQuasicoherent]
  [∀ i, (T'.term i).IsQuasicoherent] [∀ i, (T'.term i).IsFiniteType]
  (hT' : ∀ i, NegativeTerms.Above (T'.term i) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B)
  (hPure' : ∀ q, q ≠ c → (dualComplex T' n hn).ExactAt q)
  (a : KernelTowerMap.Hom T T')

@[reassoc]
abbrev naturality (i : ℕ) (hi : i + c ≤ n + 1) := by
  let (q : ℕ) : ((dualComplex T n hn).X q).IsQuasicoherent :=
    term_quasicoherent T B n hn hT hB q
  let (q : ℕ) : ((dualComplex T' n hn).X q).IsQuasicoherent :=
    term_quasicoherent T' B n hn hT' hB q
  let : Module.Injective (Projective.TopTracePairing.coefficientRing R) (Projective.TopTracePairing.coefficientRing R) :=
    Projective.SerreComplex.coefficient_injective
  have result := Trace.PureSerre.naturality
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

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.PureDuality
