import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralCanonicalNeighbors
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifts
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.BaseChange

/-! # Canonical Quotients -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! Apply the complete integral canonical quotient construction to the
original PEL lift. Rosati compatibility, polarization-degree coprimality
and level coprimality come from the original integral moduli datum. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralCanonicalNeighbors

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.GeometricPoint} (l : Lifts.IntegralLift D R b residueIso x)

theorem Lifts.IntegralLift.rosati : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation l.polarized l.action :=
  PELModuli.IntegralModel.PEL.BaseChange.rosati_pullback D.integral.universal.data.polarized D.integral.universal.data.action
    D.integral.universal.rosati l.map

variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
  (hlabels : ∀ v : Fin s, labels (v, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, false))
  (n : ℕ) (hn : 1 ≤ n) (active : Fin s) (multiplicative : Fin s → Bool)
  (Z : Over (Spec (.of R)))
  (H : Kernel.Properties.FiniteFlatKernel (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1)
    (l.action.map (j.projector iota hsplit 1 (labels (active, false))))))

def Lifts.IntegralLift.canonicalIntegralQuotient :=
  IntegralCanonicalNeighbors.integralCanonicalQuotient j iota hsplit l.polarized l.action l.rosati
    ((Nat.coprime_pow_right_iff (by decide : 0 < 2) q _).mp D.polarizationPrimeToQ)
    (Intrinsic.KernelLabels.nativeKernelLabels labels) hlabels n hn active multiplicative Z H

def Lifts.IntegralLift.canonicalIntegralQuotientAction :=
  IntegralCanonicalNeighbors.integralCanonicalQuotientAction j iota hsplit l.polarized l.action l.rosati
    ((Nat.coprime_pow_right_iff (by decide : 0 < 2) q _).mp D.polarizationPrimeToQ)
    (Intrinsic.KernelLabels.nativeKernelLabels labels) hlabels n hn active multiplicative Z H

def Lifts.IntegralLift.canonicalIntegralQuotientLevel :=
  IntegralCanonicalNeighbors.integralCanonicalQuotientLevel j iota hsplit l.polarized l.action l.rosati
    ((Nat.coprime_pow_right_iff (by decide : 0 < 2) q _).mp D.polarizationPrimeToQ)
    (Intrinsic.KernelLabels.nativeKernelLabels labels) hlabels n hn active multiplicative Z H D.levelPrimeToQ

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
