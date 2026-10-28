import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.SpecialFactor
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.ActiveIntegralInclusion
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FixedKernelCriterion
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.SpecialActiveFactors
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveMultiplicativeNormalization
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointCoordinateCriteria
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointActiveCriteria
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CoordinatePresentationFactorTransport
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FactorSquares
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointKernelComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.SourceAction
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SpecialKernelPresentations

/-! # Criterion -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Criterion

noncomputable section

/-! Transport an actual specialized active-kernel presentation through
the original geometric source comparison to the special PEL point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PELQuotient
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointKernelComparison

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
variable {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (O : D.OrdinaryKernelData j iota hsplit labels)
variable {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
variable {b : B.R →+* R}
variable {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
variable {x : D.OrdinaryPoint} (l : Lifts.IntegralLift D R b residueIso x.val)
variable (z : Targets.Lifts.EvaluatedTarget D R L b) (hbase : Lifts.ResidueCompatible D R b residueIso)

variable {n : ℕ} {Q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * (s + 1)) (Spec (.of R))}
variable (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (ActionFamilyComparison.Family.actionFamily l.actionData).abelian Q)
variable (g : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny
  ((ActionFamilyComparison.Family.actionFamily l.actionData).pullback (IntegralComparison.genericMap (R := R) (K := L)))
  ((ActionFamilyComparison.Family.actionFamily z.actionData).pullback (IntegralComparison.genericMap (R := R) (K := L))) n)
variable (hk : QuotientComparison.SameKernel (p.pullback (IntegralComparison.genericMap (R := R) (K := L))) g.isogeny)
variable (hnN : Nat.Coprime n N)
variable (hkernel : ∀ (T : Over (Spec (.of R))) (a : T ⟶ (ActionFamilyComparison.Family.actionFamily l.actionData).abelian.scheme),
  a ≫ p.hom = 1 → a ^ n = 1)

attribute [local instance] Classical.propDecidable
attribute [local irreducible] OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.finiteFlatKernel
  OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricSpecialKernel OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricLineEquiv
  Intrinsic.Neighbors.KernelPresentation.KernelOnFixed PointIsogeny.Lifts.evaluatedPointIsogeny

theorem evaluatedPointIsogeny_full_criterion (r : NumberField.RingOfIntegers E)
    (H : Intrinsic.Neighbors.KernelPresentation ((ActionFamilyComparison.Family.actionFamily l.actionData).pullback
      (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).abelian.scheme)
    (hc : ∀ (T : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))
      (a : T ⟶ ((ActionFamilyComparison.Family.actionFamily l.actionData).pullback
        (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).abelian.scheme),
      a ≫ (Over.pullback (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map (l.action.map r) = a →
      (a ≫ (p.pullback (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).hom = 1 ↔
        ∃ h : T ⟶ H.carrier, h ≫ H.inclusion = a))
    (C : OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel R L q (Lifted.OrdinarySplitting.Ordinary.liftedActiveBlock j hsplit labels l))
    (J : Submodule (ZMod q) ((Fin 2 → ZMod q) × ZMod q))
    (hV : J.map (LinearMap.fst (ZMod q) (Fin 2 → ZMod q) (ZMod q)) = ⊤)
    (hflag : decide (SubspaceCounts.Construction.identityLine ≤ J) = true)
    (hH : H = ((C.finiteFlatKernel R L q _ J).toKernelPresentation.postcomp
      (Lifted.ActiveIntegralInclusion.liftedActiveIntegralInclusion j hsplit labels l)).pullback
        (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))) :
    type_of% (show _ from by
  let K0 : Intrinsic.Neighbors.KernelPresentation (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x.val)).abelian.scheme :=
    ⟨(AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit (D.pointDatum x.val).data.polarized
        (D.pointDatum x.val).data.action (labels (0, false)) 1).X,
      AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (D.pointDatum x.val).data.polarized.abelian
        (D.pointDatum x.val).data.action 1 (labels (0, false))⟩
  have h := PointCoordinateCriteria.evaluatedPointIsogeny_coordinate_criterion
    l z hbase p g hk hnN hkernel r H hc C
    (Lifted.ActiveIntegralInclusion.liftedActiveIntegralInclusion j hsplit labels l)
    J ⊤ true hV hflag hH
  exact Intrinsic.Neighbors.KernelPresentation.KernelOnFixed.of_factor_iff (L := K0) h (fun T a =>
    Lifted.SpecialFactor.liftedSpecial_full_factor j hsplit labels l C T a)
) := by
  let K0 : Intrinsic.Neighbors.KernelPresentation (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x.val)).abelian.scheme :=
    ⟨(AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit (D.pointDatum x.val).data.polarized
        (D.pointDatum x.val).data.action (labels (0, false)) 1).X,
      AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (D.pointDatum x.val).data.polarized.abelian
        (D.pointDatum x.val).data.action 1 (labels (0, false))⟩
  have h := PointCoordinateCriteria.evaluatedPointIsogeny_coordinate_criterion
    l z hbase p g hk hnN hkernel r H hc C
    (Lifted.ActiveIntegralInclusion.liftedActiveIntegralInclusion j hsplit labels l)
    J ⊤ true hV hflag hH
  exact Intrinsic.Neighbors.KernelPresentation.KernelOnFixed.of_factor_iff (L := K0) h (fun T a =>
    Lifted.SpecialFactor.liftedSpecial_full_factor j hsplit labels l C T a)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Criterion
