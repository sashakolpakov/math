import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralSpecialChosenKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.CanonicalQuotients
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Quotients

/-! # Special Compact Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! The original lift supplies the Rosati and degree premises for the
actual integral canonical quotient's special compact components. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralCanonicalNeighbors OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralSpecialChosenKernel

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

variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
  (hlabels : ∀ v : Fin s, labels (v, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, false))
  (n : ℕ) (hn : 1 ≤ n) (active : Fin s) (multiplicative : Fin s → Bool)
  (H : Kernel.Properties.FiniteFlatKernel (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1)
    (l.action.map (j.projector iota hsplit 1 (labels (active, false))))))

theorem Lifts.IntegralLift.canonicalSpecial_compact_iff (v : Fin s) (hv : v ≠ active)
    (T : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))
    (a : T ⟶ (l.polarized.abelian.pullback
      (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).scheme)
    (ha : a ≫ (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map
      (l.action.map (j.projector iota hsplit n (labels (v, false)))) = a) :
    a ≫ ((l.canonicalIntegralQuotient j hsplit labels hlabels n hn active multiplicative
      (Over.mk (𝟙 (Spec (.of R)))) H).identitySourceIsogeny.pullback
        (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).hom = 1 ↔
      if multiplicative v then a ^ (q ^ n) = 1 else a = 1 :=
  IntegralSpecialChosenKernel.integralSpecial_compact_iff j iota hsplit l.polarized l.action l.rosati
    ((Nat.coprime_pow_right_iff (by decide : 0 < 2) q _).mp D.polarizationPrimeToQ)
    (Intrinsic.KernelLabels.nativeKernelLabels labels) hlabels n hn active multiplicative H
    (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso)) v hv T a ha

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
