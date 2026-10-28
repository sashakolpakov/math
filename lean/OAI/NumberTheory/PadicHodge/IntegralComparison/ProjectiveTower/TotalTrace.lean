import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.SerreNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.UnitTrace

/-! # Total Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.TotalTrace

noncomputable section

/-! Unit-normalized projective Serre trace before choosing a pure
cohomology degree. It is natural for the actual total dual map, so it
also applies to quotient maps onto sections of different codimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.UnitTrace (cohomology)

theorem traceFromNaturality (A : Type u) [CommRing A]
    (V₁ V₂ : ℕ → ModuleCat.{u} A) (b : ∀ q, V₁ q ⟶ V₂ q)
    {D₁ D₂ : AddCommGrpCat.{u}} {q : ℕ}
    {p₁ : D₁ ≅ DualHomologyTransport.dualGroup A (V₁ q)}
    {p₂ : D₂ ≅ DualHomologyTransport.dualGroup A (V₂ q)} {a : D₂ ⟶ D₁}
    (h : a ≫ p₁.hom = p₂.hom ≫ DualTransportNaturality.dualMap A (b q))
    (hq : q = 0) (v₁ : V₁ 0) (v₂ : V₂ 0) (hv : b 0 v₁ = v₂) :
    a ≫ SerreUnitTrace.trace A (IndexedSerreUnitTrace.pairing A V₁ p₁ hq) v₁ =
      SerreUnitTrace.trace A (IndexedSerreUnitTrace.pairing A V₂ p₂ hq) v₂ :=
  IndexedSerreTraceNaturality.trace A V₁ V₂ p₁ p₂ hq a b h v₁ v₂ hv

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

variable (T : KernelTowerResolution.Tower (C := (Proj (homogeneousSubmodule σ R)).Modules))
  [∀ q, (T.object q).IsQuasicoherent]
  [∀ q, (T.term q).IsQuasicoherent] [∀ q, (T.term q).IsFiniteType]
  (B n : ℕ) (hn : Fintype.card σ = n + 2)
  (hT : ∀ q, NegativeTerms.Above (T.term q) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B)
  (hB : n + 2 ≤ B)

def pairing := IndexedSerreUnitTrace.pairing (Projective.TopTracePairing.coefficientRing R) (UnitTrace.cohomology (T.object 0))
  (Total.serreIso T B n hn hT hB (n + 1) le_rfl) (Nat.sub_self _)

def trace (v : UnitTrace.cohomology (T.object 0) 0) :=
  SerreUnitTrace.trace (Projective.TopTracePairing.coefficientRing R) (pairing T B n hn hT hB) v

def traceIso (e : Projective.TopTracePairing.coefficientRing R ≃ₗ[Projective.TopTracePairing.coefficientRing R] UnitTrace.cohomology (T.object 0) 0) :=
  SerreUnitTrace.traceIso (Projective.TopTracePairing.coefficientRing R) (pairing T B n hn hT hB) e

theorem traceIso_hom (e : Projective.TopTracePairing.coefficientRing R ≃ₗ[Projective.TopTracePairing.coefficientRing R] UnitTrace.cohomology (T.object 0) 0) :
    (traceIso T B n hn hT hB e).hom = trace T B n hn hT hB (e 1) :=
  SerreUnitTrace.traceIso_hom _ _ e

variable {T} {T' : KernelTowerResolution.Tower (C := (Proj (homogeneousSubmodule σ R)).Modules)}
  [∀ q, (T'.object q).IsQuasicoherent]
  [∀ q, (T'.term q).IsQuasicoherent] [∀ q, (T'.term q).IsFiniteType]
  (hT' : ∀ q, NegativeTerms.Above (T'.term q) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B)
  (a : KernelTowerMap.Hom T T')

abbrev totalMap := InternalHomTotalNaturality.totalMap
  (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
  (Projective.TopTracePairing.canonicalTwist (R := R) n hn) (Trace.SerreTotalNaturality.oppositeMap a.chainMap)

abbrev naturality (v : UnitTrace.cohomology (T.object 0) 0) (v' : UnitTrace.cohomology (T'.object 0) 0)
    (hv : (TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) 0).map (a.object 0) v = v') := by
  exact traceFromNaturality (Projective.TopTracePairing.coefficientRing R)
    (UnitTrace.cohomology (T.object 0)) (UnitTrace.cohomology (T'.object 0))
    (fun q => (TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) q).map (a.object 0))
    (SerreNaturality.naturality a B n hn hT hT' hB (n + 1) le_rfl)
    (Nat.sub_self _) v v' hv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.TotalTrace
