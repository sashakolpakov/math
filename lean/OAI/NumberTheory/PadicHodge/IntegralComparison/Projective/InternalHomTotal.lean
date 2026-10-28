import OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomCechTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomTotalTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.InternalHomVanishing
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SerreComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.DualityHomology

/-! # Internal Hom Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.InternalHomTotal

noncomputable section

/-! The native Čech total of the dual resolution carries the projective
Serre pairing with the original coherent sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

variable (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] [M.IsFiniteType]
  (B n : ℕ) (hn : Fintype.card σ = n + 2)

def source : CochainComplex (Proj (homogeneousSubmodule σ R)).Modulesᵒᵖ ℕ :=
  (NegativeResolution.complex M (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B).op

def internalComplex :=
  InternalHomCechTotal.internalComplex (TopTracePairing.canonicalTwist (R := R) n hn) (source M B n hn)

def additiveTotal := InternalHomCechTotal.additiveTotal
  (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
  (TopTracePairing.canonicalTwist (R := R) n hn) (source M B n hn)

theorem terms_acyclic (hB : n + 2 ≤ B) :
    InternalHomCechTotal.TermsAcyclic (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (TopTracePairing.canonicalTwist (R := R) n hn)
      (source M B n hn) := by
  intro q p
  exact InternalHomVanishing.term_isZero M
    (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B (n + 2) hB q p

def acyclicComparisonIso (N : (Proj (homogeneousSubmodule σ R)).Modules)
    (K : CochainComplex (Proj (homogeneousSubmodule σ R)).Modulesᵒᵖ ℕ)
    (hU : iSup (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) = ⊤)
    (hK : InternalHomCechTotal.TermsAcyclic (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) N K) (d : ℕ) :
    InternalHomCechTotal.ComparisonIso (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) N K d :=
  InternalHomCechTotal.comparison.{u} (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) N
    K hU hK d

def comparisonIso (hB : n + 2 ≤ B) (d : ℕ) :=
  acyclicComparisonIso (TopTracePairing.canonicalTwist (R := R) n hn) (source M B n hn)
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))
    (terms_acyclic M B n hn hB) d

def acyclicComparisonTrans (N : (Proj (homogeneousSubmodule σ R)).Modules)
    (K : CochainComplex (Proj (homogeneousSubmodule σ R)).Modulesᵒᵖ ℕ)
    (hU : iSup (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) = ⊤)
    (hK : InternalHomCechTotal.TermsAcyclic (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) N K) (d : ℕ) {D : AddCommGrpCat.{u}}
    (e : InternalHomTotalTransport.HomologyTo N K d D) :
    InternalHomCechTotal.TotalIso (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) N K d D :=
  InternalHomTotalTransport.transport (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) N K hU hK d e

def acyclicChainComparisonTrans (N : (Proj (homogeneousSubmodule σ R)).Modules)
    (P : ChainComplex (Proj (homogeneousSubmodule σ R)).Modules ℕ)
    (hU : iSup (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) = ⊤)
    (hP : InternalHomCechTotal.TermsAcyclic (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) N P.op) (d : ℕ) {D : AddCommGrpCat.{u}}
    (e : InternalHomTotalTransport.ChainHomologyTo N P d D) :
    InternalHomCechTotal.TotalIso (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) N P.op d D :=
  acyclicComparisonTrans N P.op hU hP d (InternalHomTotalTransport.ofChain N P d e)

variable [Module.Injective R R]

def complementaryCohomology (d : ℕ) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (Module.Dual (TopTracePairing.coefficientRing R)
    ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) M
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))).homology (n + 1 - d)))

def homologyDualIso (hB : 0 < B) (d : ℕ) (hd : d ≤ n + 1) := by
  letI : Module.Injective (TopTracePairing.coefficientRing R) (TopTracePairing.coefficientRing R) :=
    SerreComplex.coefficient_injective
  exact Trace.DualityHomology.homologyIsoTo (TopTracePairing.coefficientRing R)
    (TopTracePairing.topFunctor (R := R) (σ := σ) n) (TopTracePairing.trace (R := R) n hn)
    (NegativeResolution.complex M (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B)
    (ProjectiveResolution.Duality.term_pairing_bijective M (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B n hn) d
    (ProjectiveResolution.Cohomology.comparisonIso M (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B hB n hn d hd)

def serreIso (hB : n + 2 ≤ B) (d : ℕ) (hd : d ≤ n + 1) :=
  acyclicComparisonTrans
    (TopTracePairing.canonicalTwist (R := R) n hn)
    (NegativeResolution.complex M (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B).op
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))
    (terms_acyclic M B n hn hB) d
    (homologyDualIso M B n hn (by omega) d hd)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.InternalHomTotal
