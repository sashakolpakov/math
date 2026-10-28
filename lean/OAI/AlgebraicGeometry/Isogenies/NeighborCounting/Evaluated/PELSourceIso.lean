import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionTowerIso
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PairingSourceMaps
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IteratedActionFamilyIso
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointDataSpecialization

/-! # PEL Source Iso -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PELSourceIso

noncomputable section

/-! The actual generic source comparison preserves the integral action
as well as the positive polarization, Poincare bundle and marking.
Its underlying map is the one in the original complete-kernel identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionTowerIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PairingSourceMaps.PolarizedIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PairingSourceMaps OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.SourceGroupIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IteratedActionFamilyIso.Family

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  {R F L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Field L] [Algebra R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.GeometricPoint} (l : Lifts.IntegralLift D R b residueIso x) (v : EvaluationDVRLifts.EvaluationDVR R L)

def evaluatedLiftGenericActionIso :
    PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso
      ((l.actionData.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).pullback
        (Spec.map (CommRingCat.ofHom (algebraMap F L))))
      ((l.overEvaluationDVR v).actionData.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))) :=
  (ActionTowerIso.evaluatedIntegralActionIso R F L l.actionData v).trans
    ((l.evaluationActionIso v).pullback
      (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L))))

theorem evaluatedLiftGenericActionIso_polarized :
    (evaluatedLiftGenericActionIso (F := F) l v).polarized =
      PairingSourceMaps.evaluatedPairingSourceIso (F := F) l v := by
  change (ActionTowerIso.evaluatedIntegralActionIso R F L l.actionData v).polarized.trans
    ((l.evaluationActionIso v).polarized.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))) = _
  rw [ActionTowerIso.evaluatedIntegralActionIso_polarized]
  rfl

def evaluatedGenericSourceFamilyIso :
    AbelianScheme.TateComparison.PELModuli.PELFamilyIso
      (((ActionFamilyComparison.Family.actionFamily l.actionData).pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).pullback
        (Spec.map (CommRingCat.ofHom (algebraMap F L))))
      ((ActionFamilyComparison.Family.actionFamily (l.overEvaluationDVR v).actionData).pullback
        (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))) :=
  IteratedActionFamilyIso.Family.iteratedActionFamilyIso l.actionData (l.overEvaluationDVR v).actionData
    (Spec.map (CommRingCat.ofHom (algebraMap R F)))
    (Spec.map (CommRingCat.ofHom (algebraMap F L)))
    (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))
    (evaluatedLiftGenericActionIso (F := F) l v)

theorem evaluatedGenericSourceFamilyIso_hom :
    (evaluatedGenericSourceFamilyIso (F := F) l v).abelian.hom =
      (SourceGroupIso.evaluatedLiftGenericSourceGroupIso (F := F) l v).hom.hom.hom := by
  have h := congrArg AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.abelian
    (evaluatedLiftGenericActionIso_polarized (F := F) l v)
  exact (IteratedActionFamilyIso.Family.iteratedActionFamilyIso_hom l.actionData (l.overEvaluationDVR v).actionData
    (Spec.map (CommRingCat.ofHom (algebraMap R F)))
    (Spec.map (CommRingCat.ofHom (algebraMap F L)))
    (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))
    (evaluatedLiftGenericActionIso (F := F) l v)).trans
      ((congrArg Iso.hom h).trans (PairingSourceMaps.evaluatedPairingSourceMap_eq (F := F) l v))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PELSourceIso
