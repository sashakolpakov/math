import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralSpecialActiveCriteria
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointActiveCriteria
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.PresentationComposition

/-! # Active Point Carrier -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActivePointCarrier.ReferencePresentation

/-! Name the actual specialized active carrier and its inclusion in
the original geometric source PEL point before comparing the quotients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedActiveEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinateSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralActiveKernels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralQuotients OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralSpecialActiveCriteria
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets

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

def originalActivePointPresentation :
    Intrinsic.Neighbors.KernelPresentation (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x.val)).abelian.scheme :=
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  (IntegralSpecialActiveCriteria.originalActiveSpecialPresentation j hsplit labels O l hTorsionQuotient a i p).postcomp
    (l.overEvaluationDVR v).geometricFamilyIso.abelian.hom

end AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActivePointCarrier.ReferencePresentation

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActivePointCarrier

/-! Identify the identical actual active carriers before invoking the
full special PEL isogeny, retaining the original inclusion square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedActiveEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinateSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralActiveKernels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralQuotients OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralSpecialActiveCriteria OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActivePointCarrier.ReferencePresentation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets

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

def originalActivePointCarrierIso :
    (IntegralSpecialActiveCriteria.originalActiveSpecialPresentation j hsplit labels O l hTorsionQuotient a i p).carrier ≅
      (ReferencePresentation.originalActivePointPresentation j hsplit labels O l hTorsionQuotient a i p).carrier :=
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  (IntegralSpecialActiveCriteria.originalActiveSpecialPresentation j hsplit labels O l hTorsionQuotient a i p).postcompCarrierIso
    (l.overEvaluationDVR v).geometricFamilyIso.abelian.hom

theorem originalActivePointCarrierIso_inclusion :
    type_of% (
      letI := a.evaluation.scalarAlgebra R
      letI := a.evaluation.scalarTower R
      let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
      (IntegralSpecialActiveCriteria.originalActiveSpecialPresentation j hsplit labels O l hTorsionQuotient a i p).postcompCarrierIso_inclusion
        (l.overEvaluationDVR v).geometricFamilyIso.abelian.hom) := by
  let := a.evaluation.scalarAlgebra R
  let := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  exact (IntegralSpecialActiveCriteria.originalActiveSpecialPresentation j hsplit labels O l hTorsionQuotient a i p).postcompCarrierIso_inclusion
    (l.overEvaluationDVR v).geometricFamilyIso.abelian.hom

end AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActivePointCarrier

end

end OAI
