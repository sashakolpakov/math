import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.GenericActiveKernels
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CoordinateSubspaces
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitKernelParameterComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrimeBlockSplitting
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CoordinateKernelDetection

/-! # Active Kernel Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActiveKernelComparison

noncomputable section

/-! The constructed integral active kernel has exactly the original
parameter's generic subgroup, as a modeled functor on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedActiveEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinateSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.GenericActiveKernels OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupPointBaseChange
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveChoiceImage.Prime OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CoordinateSubspaces.IntrinsicRationalMembership
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrimeBlockSplitting OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitKernelParameterComparison
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (O : D.OrdinaryKernelData j iota hsplit labels)
  {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  [Field L] [CharZero L] [Algebra R L] [IsFractionRing R L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.OrdinaryPoint} (l : Lifts.IntegralLift D R b residueIso x.val) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)

local instance neighborProjector_group (i : Fin 3) (v : Fin (s + 1)) :
    IsMonHom (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l i v) :=
  (l.genericAction (L := L)).preservesGroup
    (j.projector iota hsplit (HeckeExponents.neighborLevel i) (labels (v, false)))

variable (a : ConstructedActiveEvaluation.LiftedActiveEvaluation (L := L) j hsplit labels O l hTorsionQuotient)

variable (i : Fin 3) (p : ULift (Fin (a.evaluation.count (some i))))

def originalActiveSubgroup :
    AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q ((l.genericAction (L := L)).map (j.projector iota hsplit 1 (labels (0, false)))))
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L a.evaluation.carrier)))) :=
  Evaluated.ActiveChoiceImage.Prime.evaluatedPrimeActiveSubgroup j iota hsplit (l.genericPolarized (L := L)).abelian
    (l.genericAction (L := L)) (O.compact x)
    (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l) hTorsionQuotient a.evaluation i (labels (0, false)) p

def originalActiveSubgroupModel : (originalActiveSubgroup j hsplit labels O l hTorsionQuotient a i p).Model :=
  Evaluated.ActiveChoiceImage.Prime.evaluatedPrimeActiveSubgroupModel j iota hsplit (l.genericPolarized (L := L)).abelian
    (l.genericAction (L := L)) (O.compact x)
    (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l) hTorsionQuotient a.evaluation i (labels (0, false)) rfl p

/-- Keep the proved equality in a data wrapper so its concrete type is inferred. -/
def originalActiveKernelIdentity :=
  let D₀ := CoordinateSubspaces.originalCoordinateKernelParameters j hsplit labels O l hTorsionQuotient a i
  let f := Spec.map (CommRingCat.ofHom (algebraMap L a.evaluation.carrier))
  let p₁ := (l.genericAction (L := L)).map (j.projector iota hsplit 1 (labels (0, false)))
  let e := PrimeBlockSplitting.primeBlockSplitIso q p₁ f a.blockIso
  PLift.up (D₀.kernel_eq e p)

theorem originalActiveKernel_generic_eq :
    type_of% (originalActiveKernelIdentity j hsplit labels O l hTorsionQuotient a i p).down :=
  (originalActiveKernelIdentity j hsplit labels O l hTorsionQuotient a i p).down

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActiveKernelComparison
