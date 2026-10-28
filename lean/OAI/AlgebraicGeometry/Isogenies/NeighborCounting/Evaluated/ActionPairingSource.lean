import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PairingSourceMaps
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionPairingSourceData
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointDataSpecialization

/-! # Action Pairing Source -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActionPairingSource

noncomputable section

/-! Construct the coherent pairing comparison of the original generic action datum and the actual evaluated integral action datum. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockGroupComparison
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedTowerIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.SourceGroupIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedIsoCanonicalPairing

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

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PairingSourceMaps.PolarizedIso

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionPairingSourceData OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PairingSourceMaps

abbrev genericActionData :
    PELModuli.IntegralModel.PEL.Has.PolarizedActionData E (3 * s) P.polarizationType N (Spec (.of F)) where
  polarized := l.polarized.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))
  action := l.action.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))

abbrev evaluatedActionData :
    PELModuli.IntegralModel.PEL.Has.PolarizedActionData E (3 * s) P.polarizationType N (Spec (.of v.carrier)) where
  polarized := (l.overEvaluationDVR v).polarized
  action := (l.overEvaluationDVR v).action

def evaluatedActionPairingSource :
    ActionPairingSourceData.ActionPairingSource
      (genericActionData (F := F) l)
      (evaluatedActionData l v)
      (Spec.map (CommRingCat.ofHom (algebraMap F L)))
      (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L))) where
  iso := PairingSourceMaps.evaluatedPairingSourceIso (F := F) l v
  groupIso := SourceGroupIso.evaluatedLiftGenericSourceGroupIso (F := F) l v
  map_eq := PairingSourceMaps.evaluatedPairingSourceMap_eq (F := F) l v

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActionPairingSource
