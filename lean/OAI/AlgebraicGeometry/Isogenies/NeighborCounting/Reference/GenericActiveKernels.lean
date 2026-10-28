import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralActiveKernels
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.GenericActiveKernel

/-! # Generic Active Kernels -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.GenericActiveKernels

noncomputable section

/-! Transport the constructed integral kernel for every literal original
parameter into the original generic source, retaining its actual model
and its original evaluated-coordinate membership criterion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedActiveEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinateSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.GenericActiveKernel OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupPointBaseChange
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

abbrev originalGenericActiveKernel :
    Kernel.Properties.FiniteFlatKernel ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap L a.evaluation.carrier)))).obj
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q ((l.genericAction (L := L)).map (j.projector iota hsplit 1 (labels (0, false)))))) :=
  (CoordinateSubspaces.originalEvaluatedCoordinateData j hsplit labels O l hTorsionQuotient a).kernel
    (CoordinateSubspaces.originalCoordinateSubspaceEquiv j hsplit labels O l hTorsionQuotient a i p).val

theorem originalGenericActiveKernel_membership
    (z : Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L a.evaluation.carrier))) ⟶
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q ((l.genericAction (L := L)).map (j.projector iota hsplit 1 (labels (0, false)))))) :
    let C := CoordinateSubspaces.originalEvaluatedCoordinateData j hsplit labels O l hTorsionQuotient a
    let J := (CoordinateSubspaces.originalCoordinateSubspaceEquiv j hsplit labels O l hTorsionQuotient a i p).val
    C.coordinates z ∈ J ↔
      ∃ b : Over.mk (𝟙 (Spec (.of a.evaluation.carrier))) ⟶ (C.kernel J).carrier,
        b ≫ (C.kernel J).inclusion =
          GroupPointBaseChange.pointPullbackGroupEquiv (Spec.map (CommRingCat.ofHom (algebraMap L a.evaluation.carrier)))
            (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q
              ((l.genericAction (L := L)).map (j.projector iota hsplit 1 (labels (0, false)))))) z.toMul := by
  let C := CoordinateSubspaces.originalEvaluatedCoordinateData j hsplit labels O l hTorsionQuotient a
  let J := (CoordinateSubspaces.originalCoordinateSubspaceEquiv j hsplit labels O l hTorsionQuotient a i p).val
  exact C.membership J z

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.GenericActiveKernels
