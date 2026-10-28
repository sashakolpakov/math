import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GenericActiveCoordinateData
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CoordinateKernelDetection
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.OrdinaryCoordinates
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.EvaluatedSubspaces
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CoordinateEnumeration
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CoordinateSubspaces
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Coordinate Subspaces -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinateSubspaces

noncomputable section

/-! The original finite parameter labels enumerate standard active
subspaces through the actual evaluated integral ordinary coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedActiveEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.EvaluatedSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCoordinates
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces

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

def originalEvaluatedCoordinateData :
    GenericActiveCoordinateData.ActiveCoordinateData
      (Spec.map (CommRingCat.ofHom (algebraMap L a.evaluation.carrier)))
      (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q ((l.genericAction (L := L)).map
        (j.projector iota hsplit 1 (labels (0, false)))))) q := by
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  exact GenericActiveCoordinateData.evaluatedActiveCoordinateData (F := L) j hsplit labels O l
    (ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a) a.blockIso

abbrev originalEvaluatedLinearCoordinates :
    Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L a.evaluation.carrier))) ⟶
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q ((l.genericAction (L := L)).map (j.projector iota hsplit 1 (labels (0, false))))) ≃ₗ[ZMod q]
        ((Fin 2 → ZMod q) × ZMod q) :=
  (originalEvaluatedCoordinateData j hsplit labels O l hTorsionQuotient a).coordinates

def originalParameterCoordinateData (i : Fin 3) :=
  Intrinsic.CoordinateSubspaces.nativeParameterCoordinateData
    j hsplit labels O l hTorsionQuotient a.evaluation i
    (AlgebraicClosure a.evaluation.carrier)
    (algebraMap a.evaluation.carrier (AlgebraicClosure a.evaluation.carrier))
    (originalEvaluatedCoordinateData j hsplit labels O l hTorsionQuotient a).coordinates.toAddEquiv

def originalCoordinateKernelParameters (i : Fin 3) :=
  Intrinsic.CoordinateSubspaces.nativeCoordinateKernelParameters
    j hsplit labels O l hTorsionQuotient a.evaluation i
    (AlgebraicClosure a.evaluation.carrier)
    (algebraMap a.evaluation.carrier (AlgebraicClosure a.evaluation.carrier))
    (originalEvaluatedCoordinateData j hsplit labels O l hTorsionQuotient a)

abbrev originalCoordinateSubspaceEquiv (i : Fin 3) :
    ULift (Fin (a.evaluation.count (some i))) ≃
      {J : Submodule (ZMod q) ((Fin 2 → ZMod q) × ZMod q) //
        Module.finrank (ZMod q) J = HeckeExponents.neighborLevel i} :=
  (originalCoordinateKernelParameters j hsplit labels O l hTorsionQuotient a i).enumeration

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinateSubspaces
