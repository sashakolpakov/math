import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.GeometricActivePresentation
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.SpecialActiveFactors
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.SpecialFactor
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActivePointCarrier
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.ActivePointPresentation
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActiveSpecialKernels

/-! # Coordinate Point Factors -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinatePointFactors.ReferencePresentation

/-! The original evaluated geometry has an actual point presentation
for each active special subgroup and a constructed independent line permutation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedActiveEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinateSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralActiveKernels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralQuotients OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralSpecialActiveCriteria OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActivePointCarrier.ReferencePresentation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationDVROrdinaryCoordinates.Ordinary OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActiveSpecialKernels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCounts.Construction
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets
attribute [local instance] Classical.propDecidable

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

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.GeometricActivePresentation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.SpecialActiveFactors
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.SpecialFactor OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.BlockInclusions OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.OrdinarySplitting.Ordinary

abbrev originalProjection (i : Fin 3) (p : ULift (Fin (a.evaluation.count (some i)))) :=
  (CoordinateSubspaces.originalCoordinateSubspaceEquiv j hsplit labels O l hTorsionQuotient a i p).val.map
    (LinearMap.fst (ZMod q) (Fin 2 → ZMod q) (ZMod q))

abbrev originalIdentityFlag (i : Fin 3) (p : ULift (Fin (a.evaluation.count (some i)))) : Bool :=
  decide (SubspaceCounts.Construction.identityLine ≤ (CoordinateSubspaces.originalCoordinateSubspaceEquiv j hsplit labels O l hTorsionQuotient a i p).val)

def originalCoordinatePointPresentation
    (V : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q)) (flag : Bool) :
    Intrinsic.Neighbors.KernelPresentation (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x.val)).abelian.scheme :=
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  let C := EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel (F := L) j hsplit labels O l v a.blockIso
  (C.geometricSpecialKernel v.carrier a.evaluation.carrier q _ (residueIso.trans v.residueIso)
    V flag).postcomp
      ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso.trans v.residueIso))).map
        (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) ((l.overEvaluationDVR v).action.map
          (j.projector iota hsplit 1 (labels (0, false))))) ≫
            (l.overEvaluationDVR v).geometricFamilyIso.abelian.hom)

def originalSpecialLineEquiv : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q ≃ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q :=
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  let C := EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel (F := L) j hsplit labels O l v a.blockIso
  C.geometricLineEquiv v.carrier a.evaluation.carrier q _ (residueIso.trans v.residueIso)
    (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.activeOrdinarySplitting (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (O.splitting x 1 0))
    (Geometric.BlockInclusions.liftedGeometricOriginalBlockIso j hsplit labels (l.overEvaluationDVR v) 1 0)

end AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinatePointFactors.ReferencePresentation

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinatePointFactors

/-! All five actual evaluated active specializations have their native
factorization criteria inside the original geometric source point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedActiveEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinateSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralActiveKernels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralQuotients OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralSpecialActiveCriteria OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActivePointCarrier.ReferencePresentation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationDVROrdinaryCoordinates.Ordinary OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActiveSpecialKernels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCounts.Construction
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets
attribute [local instance] Classical.propDecidable

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

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.GeometricActivePresentation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.SpecialActiveFactors
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.SpecialFactor OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.BlockInclusions OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.OrdinarySplitting.Ordinary

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinatePointFactors.ReferencePresentation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveMixedLineTransport
open _root_.CategoryTheory.MonoidalCategory

attribute [local irreducible] OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricSpecialKernel
  OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricLineEquiv EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel
  ConstructedActiveEvaluation.activeEvaluationDVR Lifts.IntegralLift.overEvaluationDVR

omit [IsGalois ℚ E] in
theorem originalCoordinate_graph_line_factor (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q)
    (T : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))
    (z : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme) :
    type_of% (
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  let C := EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel (F := L) j hsplit labels O l v a.blockIso
  Lifted.SpecialActiveFactors.liftedSpecial_graph_line_factor j hsplit labels O (l.overEvaluationDVR v) C J T z) := by
  let := a.evaluation.scalarAlgebra R
  let := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  let C := EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel (F := L) j hsplit labels O l v a.blockIso
  exact Lifted.SpecialActiveFactors.liftedSpecial_graph_line_factor j hsplit labels O (l.overEvaluationDVR v) C J T z

omit [IsGalois ℚ E] in
theorem originalCoordinate_mixed_line_factor (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q)
    (T : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))
    (z : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme) :
    type_of% (
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  let C := EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel (F := L) j hsplit labels O l v a.blockIso
  Lifted.SpecialActiveFactors.liftedSpecial_mixed_line_factor j hsplit labels O (l.overEvaluationDVR v) C J T z) := by
  let := a.evaluation.scalarAlgebra R
  let := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  let C := EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel (F := L) j hsplit labels O l v a.blockIso
  exact Lifted.SpecialActiveFactors.liftedSpecial_mixed_line_factor j hsplit labels O (l.overEvaluationDVR v) C J T z

omit [IsGalois ℚ E] in
theorem originalCoordinate_plane_factor
    (T : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))
    (z : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme) :
    type_of% (
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  let C := EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel (F := L) j hsplit labels O l v a.blockIso
  Lifted.SpecialActiveFactors.liftedSpecial_plane_factor j hsplit labels O (l.overEvaluationDVR v) C T z) := by
  let := a.evaluation.scalarAlgebra R
  let := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  let C := EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel (F := L) j hsplit labels O l v a.blockIso
  exact Lifted.SpecialActiveFactors.liftedSpecial_plane_factor j hsplit labels O (l.overEvaluationDVR v) C T z

omit [IsGalois ℚ E] in
theorem originalCoordinate_multiplicative_factor
    (T : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))
    (z : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme) :
    type_of% (
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  let C := EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel (F := L) j hsplit labels O l v a.blockIso
  Lifted.SpecialActiveFactors.liftedSpecial_multiplicative_factor j hsplit labels O (l.overEvaluationDVR v) C T z) := by
  let := a.evaluation.scalarAlgebra R
  let := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  let C := EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel (F := L) j hsplit labels O l v a.blockIso
  exact Lifted.SpecialActiveFactors.liftedSpecial_multiplicative_factor j hsplit labels O (l.overEvaluationDVR v) C T z

omit [IsGalois ℚ E] in
theorem originalCoordinate_full_factor
    (T : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))
    (z : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme) :
    type_of% (
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  let C := EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel (F := L) j hsplit labels O l v a.blockIso
  Lifted.SpecialFactor.liftedSpecial_full_factor j hsplit labels (l.overEvaluationDVR v) C T z) := by
  let := a.evaluation.scalarAlgebra R
  let := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  let C := EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel (F := L) j hsplit labels O l v a.blockIso
  exact Lifted.SpecialFactor.liftedSpecial_full_factor j hsplit labels (l.overEvaluationDVR v) C T z

end AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinatePointFactors

end

end OAI
