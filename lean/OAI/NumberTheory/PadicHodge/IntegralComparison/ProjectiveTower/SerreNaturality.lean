import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.Total
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.CohomologyNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.SerreTotalNaturality

/-! # Serre Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.SerreNaturality

noncomputable section

/-! The complete Serre comparison is natural under the actual maps of
negative projective kernel towers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite

set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

variable {T T' : KernelTowerResolution.Tower (C := (Proj (homogeneousSubmodule σ R)).Modules)}
  [∀ i, (T.object i).IsQuasicoherent] [∀ i, (T'.object i).IsQuasicoherent]
  [∀ i, (T.term i).IsQuasicoherent] [∀ i, (T'.term i).IsQuasicoherent]
  [∀ i, (T.term i).IsFiniteType] [∀ i, (T'.term i).IsFiniteType]
  (a : KernelTowerMap.Hom T T') (B n : ℕ) (hn : Fintype.card σ = n + 2)
  (hT : ∀ i, NegativeTerms.Above (T.term i) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B)
  (hT' : ∀ i, NegativeTerms.Above (T'.term i) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B)
  (hB : n + 2 ≤ B)

@[reassoc]
theorem naturality (d : ℕ) (hd : d ≤ n + 1) :
    HomologicalComplex.homologyMap
      (InternalHomTotalNaturality.totalMap
        (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
        (Projective.TopTracePairing.canonicalTwist (R := R) n hn) (Trace.SerreTotalNaturality.oppositeMap a.chainMap)) d ≫
      (Total.serreIso T B n hn hT hB d hd).hom =
    (Total.serreIso T' B n hn hT' hB d hd).hom ≫
      DualTransportNaturality.dualMap (Projective.TopTracePairing.coefficientRing R)
        ((TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
          (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (n + 1 - d)).map (a.object 0)) := by
  let : Module.Injective (Projective.TopTracePairing.coefficientRing R) (Projective.TopTracePairing.coefficientRing R) :=
    Projective.SerreComplex.coefficient_injective
  have result := Trace.SerreTotalNaturality.naturality
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
    (Projective.TopTracePairing.coefficientRing R) (Projective.TopTracePairing.topFunctor (R := R) (σ := σ) n) (Projective.TopTracePairing.canonicalTwist (R := R) n hn)
    (Projective.TopTracePairing.trace (R := R) n hn) a.chainMap
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))
    (fun i => Projective.TopDuality.pairing_bijective n hn (T.term i))
    (fun i => Projective.TopDuality.pairing_bijective n hn (T'.term i))
    (Total.terms_acyclic T B n hn hT hB)
    (Total.terms_acyclic T' B n hn hT' hB) d
    (Duality.cohomologyIso T n hn
      (Total.lower_vanishing T B n hn hT hB) d hd)
    (Duality.cohomologyIso T' n hn
      (Total.lower_vanishing T' B n hn hT' hB) d hd) _
    (CohomologyNaturality.naturality a n hn
      (Total.lower_vanishing T B n hn hT hB)
      (Total.lower_vanishing T' B n hn hT' hB) d hd)
  convert result using 3 <;> rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.SerreNaturality
